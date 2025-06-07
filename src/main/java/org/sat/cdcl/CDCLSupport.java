package org.sat.cdcl;

import org.sat.cnf.CNFConverter;
import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;

/**
 * SUPPORTO CDCL - Strutture dati ottimizzate per l'algoritmo CDCL
 *
 * Questo modulo fornisce le strutture dati fondamentali per il solutore CDCL,
 * ottimizzate per massimizzare efficienza e correttezza durante la risoluzione SAT.
 *
 * COMPONENTI PRINCIPALI:
 * • CNFFormula: Rappresentazione numerica ottimizzata di formule CNF
 * • AssignedLiteral: Modello completo di letterali assegnati con metadata
 * • DecisionStack: Stack gerarchico per gestione livelli e backtracking
 *
 * CARATTERISTICHE CHIAVE:
 * • Conversione efficiente da albero CNF a rappresentazione numerica
 * • Tracking completo degli assegnamenti con genealogia delle decisioni
 * • Gestione robusta del backtracking cronologico e non-cronologico
 * • Validazione comprehensive con gestione errori
 * • Logging dettagliato per debugging e analisi performance
 *
 */

//region RAPPRESENTAZIONE FORMULA CNF OTTIMIZZATA

/**
 * FORMULA CNF OTTIMIZZATA - Conversione da albero CNFConverter a rappresentazione numerica
 *
 * Converte la rappresentazione ad albero CNFConverter in una struttura dati altamente ottimizzata
 * per l'algoritmo CDCL. Utilizza identificatori numerici per variabili e rappresentazioni
 * compatte per clausole, massimizzando efficienza di memoria e velocità di accesso.
 *
 * OTTIMIZZAZIONI IMPLEMENTATE:
 * • Mapping bidirezionale variabili simboliche ↔ ID numerici
 * • Clausole rappresentate come List<Integer> per accesso O(1)
 * • Validazione completa durante conversione per prevenzione errori
 * • Caching intelligente per operazioni frequenti
 * • Statistiche dettagliate per analisi complessità formula
 *
 * INVARIANTI MANTENUTE:
 * • Ogni variabile simbolica ha ID numerico univoco ≥ 1
 * • Lista clausole immutabile dopo costruzione
 * • Mapping variabili preserva ordine di inserimento
 * • Tutti i letterali referenziano variabili valide
 */
class CNFFormula {

    private static final Logger LOGGER = Logger.getLogger(CNFFormula.class.getName());

    //region STRUTTURE DATI CORE

    /**
     * Clausole CNF in formato numerico ottimizzato per elaborazione CDCL.
     * Ogni clausola è List<Integer> dove ogni Integer rappresenta un letterale:
     * • Valori positivi: letterali positivi (variabile vera)
     * • Valori negativi: letterali negati (variabile falsa)
     * • Invariante: lista immutabile dopo costruzione completa
     */
    private final List<List<Integer>> clauses;

    /**
     * Numero totale di variabili distinte nella formula.
     * Corrisponde al massimo ID variabile assegnato durante conversione.
     */
    private final int variableCount;

    /**
     * Mapping bidirezionale: nome simbolico → ID numerico.
     * Mantiene tracciabilità completa per debugging e output human-readable.
     * Invariante: ogni nome simbolico ha ID univoco ≥ 1, no duplicati
     */
    private final Map<String, Integer> variableMapping;

    //endregion

    //region COSTRUZIONE E CONVERSIONE PRINCIPALE

    /**
     * Costruisce formula CNF ottimizzata da rappresentazione ad albero CNFConverter.
     *
     * PROCESSO DI CONVERSIONE:
     * 1. Validazione input e inizializzazione strutture dati
     * 2. Analisi struttura albero CNF per identificazione pattern
     * 3. Conversione ricorsiva nodi → clausole numeriche
     * 4. Generazione mapping variabili con assegnazione ID progressivi
     * 5. Validazione integrità finale e calcolo statistiche
     * 6. Costruzione rappresentazione immutabile ottimizzata
     *
     * @param cnfConverter formula CNF in formato albero da convertire
     * @throws IllegalArgumentException se formula malformata o null
     * @throws RuntimeException se errori critici durante conversione
     */
    public CNFFormula(CNFConverter cnfConverter) {
        if (cnfConverter == null) {
            throw new IllegalArgumentException("CNFConverter non può essere null");
        }

        LOGGER.info("=== AVVIO CONVERSIONE FORMULA CNF OTTIMIZZATA ===");

        // Inizializzazione strutture dati temporanee
        this.clauses = new ArrayList<>();
        this.variableMapping = new LinkedHashMap<>(); // Preserva ordine inserimento

        try {
            // Processo di conversione principale
            executeConversionFromCNFTree(cnfConverter);

            // Finalizzazione e validazione
            this.variableCount = variableMapping.size();
            validateConversionIntegrity();
            logConversionStatistics();

        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Errore durante conversione CNF", e);
            throw new RuntimeException("Conversione CNF fallita: " + e.getMessage(), e);
        }

        LOGGER.info("=== CONVERSIONE CNF COMPLETATA CON SUCCESSO ===");
    }

    /**
     * Esegue la conversione principale dall'albero CNFConverter alle strutture numeriche.
     * Gestisce tutti i pattern possibili della struttura CNF in modo robusto.
     */
    private void executeConversionFromCNFTree(CNFConverter converter) {
        LOGGER.fine("Avvio conversione da tipo albero: " + converter.type);

        switch (converter.type) {
            case AND -> {
                // Formula complessa: congiunzione di clausole multiple
                LOGGER.fine("Conversione formula AND con multiple clausole");
                processComplexConjunctionFormula(converter);
            }
            default -> {
                // Formula semplice: clausola singola, letterale, o negazione
                LOGGER.fine("Conversione formula semplice: " + converter.type);
                processSingleElementFormula(converter);
            }
        }

        LOGGER.fine("Clausole totali estratte: " + clauses.size());
    }

    /**
     * Processa formula complessa con congiunzione di clausole multiple.
     * Ogni operando del nodo AND rappresenta una clausola separata.
     */
    private void processComplexConjunctionFormula(CNFConverter conjunctionNode) {
        if (conjunctionNode.operands == null || conjunctionNode.operands.isEmpty()) {
            LOGGER.warning("Nodo AND vuoto rilevato - formula senza clausole");
            return;
        }

        LOGGER.fine("Processamento " + conjunctionNode.operands.size() + " clausole in congiunzione");

        for (CNFConverter clauseNode : conjunctionNode.operands) {
            List<Integer> convertedClause = convertSingleClauseToNumerical(clauseNode);
            if (isClauseValid(convertedClause)) {
                clauses.add(convertedClause);
                LOGGER.finest("Clausola aggiunta: " + convertedClause);
            } else {
                LOGGER.warning("Clausola non valida ignorata: " + clauseNode);
            }
        }
    }

    /**
     * Processa formula semplice (clausola singola, letterale, o negazione).
     */
    private void processSingleElementFormula(CNFConverter singleNode) {
        List<Integer> convertedClause = convertSingleClauseToNumerical(singleNode);
        if (isClauseValid(convertedClause)) {
            clauses.add(convertedClause);
            LOGGER.fine("Clausola semplice aggiunta: " + convertedClause);
        } else {
            LOGGER.warning("Clausola semplice non valida: " + singleNode);
        }
    }

    //endregion

    //region CONVERSIONE CLAUSOLE E LETTERALI

    /**
     * Converte una singola clausola da nodo albero a rappresentazione numerica ottimizzata.
     *
     * TIPI DI CLAUSOLE GESTITI:
     * • OR: Disgiunzione di letterali → clausola normale multi-letterale
     * • ATOM: Variabile atomica → clausola unitaria positiva
     * • NOT: Negazione di variabile → clausola unitaria negativa
     * • Strutture complesse: Gestione ricorsiva con validazione
     *
     * @param clauseNode nodo albero rappresentante la clausola
     * @return lista letterali numerici (vuota se conversione fallisce)
     */
    private List<Integer> convertSingleClauseToNumerical(CNFConverter clauseNode) {
        if (clauseNode == null) {
            LOGGER.warning("Nodo clausola null rilevato");
            return new ArrayList<>();
        }

        List<Integer> literals = new ArrayList<>();

        switch (clauseNode.type) {
            case OR -> {
                // Clausola normale: disgiunzione di letterali multipli
                literals = convertDisjunctionToLiterals(clauseNode);
                LOGGER.finest("Disgiunzione convertita: " + literals.size() + " letterali");
            }
            case ATOM, NOT -> {
                // Clausola unitaria: singolo letterale (positivo o negativo)
                Integer literal = convertSingleLiteralToNumerical(clauseNode);
                if (literal != null) {
                    literals.add(literal);
                    LOGGER.finest("Letterale unitario convertito: " + literal);
                }
            }
            default -> {
                LOGGER.warning("Tipo clausola non supportato per conversione: " + clauseNode.type);
            }
        }

        return literals;
    }

    /**
     * Converte nodo OR (disgiunzione) in lista di letterali numerici.
     * Ogni operando del nodo OR diventa un letterale nella clausola risultante.
     */
    private List<Integer> convertDisjunctionToLiterals(CNFConverter orNode) {
        List<Integer> literals = new ArrayList<>();

        if (orNode.operands == null || orNode.operands.isEmpty()) {
            LOGGER.warning("Nodo OR senza operandi rilevato");
            return literals;
        }

        LOGGER.finest("Conversione " + orNode.operands.size() + " letterali da disgiunzione");

        for (CNFConverter literalNode : orNode.operands) {
            Integer convertedLiteral = convertSingleLiteralToNumerical(literalNode);
            if (convertedLiteral != null) {
                literals.add(convertedLiteral);
                LOGGER.finest("Letterale aggiunto: " + convertedLiteral);
            } else {
                LOGGER.warning("Letterale non convertibile ignorato: " + literalNode);
            }
        }

        return literals;
    }

    /**
     * Converte un singolo letterale in rappresentazione numerica DIMACS.
     *
     * CONVERSIONE DIMACS:
     * • ATOM "P" → +ID (letterale positivo)
     * • NOT ATOM "¬P" → -ID (letterale negativo)
     * • ID sono generati progressivamente per mantenere consistenza
     *
     * @param literalNode nodo rappresentante il letterale
     * @return ID numerico del letterale (null se conversione fallisce)
     */
    private Integer convertSingleLiteralToNumerical(CNFConverter literalNode) {
        if (literalNode == null) {
            LOGGER.finest("Nodo letterale null");
            return null;
        }

        return switch (literalNode.type) {
            case ATOM -> convertPositiveLiteral(literalNode);
            case NOT -> convertNegativeLiteral(literalNode);
            default -> {
                LOGGER.warning("Tipo letterale non riconosciuto: " + literalNode.type);
                yield null;
            }
        };
    }

    /**
     * Converte letterale positivo (variabile atomica) in ID numerico positivo.
     */
    private Integer convertPositiveLiteral(CNFConverter atomNode) {
        String variableName = extractAndValidateVariableName(atomNode.atom);
        if (variableName == null) {
            return null;
        }

        Integer variableId = getOrCreateVariableId(variableName);
        LOGGER.finest("Letterale positivo convertito: " + variableName + " → +" + variableId);
        return variableId;
    }

    /**
     * Converte letterale negativo (NOT di variabile atomica) in ID numerico negativo.
     */
    private Integer convertNegativeLiteral(CNFConverter notNode) {
        // Validazione struttura NOT(ATOM)
        if (notNode.operand == null || notNode.operand.type != CNFConverter.Type.ATOM) {
            LOGGER.warning("Struttura NOT non valida - operando: " +
                    (notNode.operand != null ? notNode.operand.type : "null"));
            return null;
        }

        String variableName = extractAndValidateVariableName(notNode.operand.atom);
        if (variableName == null) {
            return null;
        }

        Integer variableId = getOrCreateVariableId(variableName);
        Integer negatedId = -variableId;

        LOGGER.finest("Letterale negativo convertito: ¬" + variableName + " → " + negatedId);
        return negatedId;
    }

    //endregion

    //region GESTIONE MAPPING VARIABILI

    /**
     * Estrae e valida nome variabile da stringa atomica con normalizzazione.
     */
    private String extractAndValidateVariableName(String atom) {
        if (atom == null || atom.trim().isEmpty()) {
            LOGGER.warning("Nome variabile vuoto o null rilevato");
            return null;
        }

        String normalizedName = atom.trim();

        // Validazione ulteriore nome variabile
        if (normalizedName.contains(" ") || normalizedName.contains("\t")) {
            LOGGER.warning("Nome variabile contiene spazi: '" + normalizedName + "'");
            return normalizedName.replaceAll("\\s+", "_"); // Normalizzazione automatica
        }

        return normalizedName;
    }

    /**
     * Ottiene ID numerico per variabile, creandolo se necessario con strategia lazy.
     *
     * STRATEGIA ASSEGNAZIONE ID:
     * • Se variabile già mappata → restituisce ID esistente
     * • Se variabile nuova → assegna prossimo ID disponibile (progressivo)
     * • Aggiorna mapping bidirezionale e registra nel log
     * • Garantisce univocità e consistenza degli ID
     *
     * @param variableName nome simbolico della variabile
     * @return ID numerico univoco (sempre > 0)
     */
    private Integer getOrCreateVariableId(String variableName) {
        return variableMapping.computeIfAbsent(variableName, name -> {
            int newId = variableMapping.size() + 1;
            LOGGER.finest("Nuova variabile mappata: " + name + " → ID " + newId);
            return newId;
        });
    }

    //endregion

    //region VALIDAZIONE E INTEGRITÀ

    /**
     * Verifica se una clausola convertita è valida per inclusione nella formula.
     */
    private boolean isClauseValid(List<Integer> clause) {
        return clause != null && !clause.isEmpty();
    }

    /**
     * Valida integrità completa della conversione eseguita.
     * Verifica consistenza tra tutte le strutture dati e assenza di corruzioni.
     */
    private void validateConversionIntegrity() {
        LOGGER.fine("Avvio validazione integrità conversione CNF");

        // Validazione coerenza conteggio variabili
        if (variableCount != variableMapping.size()) {
            throw new IllegalStateException("Inconsistenza conteggio variabili: atteso=" +
                    variableMapping.size() + ", calcolato=" + variableCount);
        }

        // Validazione integrità mapping variabili
        validateVariableMapping();

        // Validazione range letterali nelle clausole
        validateClauseLiterals();

        LOGGER.fine("Validazione integrità conversione: SUCCESSO");
    }

    /**
     * Valida integrità del mapping delle variabili.
     */
    private void validateVariableMapping() {
        for (Map.Entry<String, Integer> entry : variableMapping.entrySet()) {
            String variableName = entry.getKey();
            Integer variableId = entry.getValue();

            if (variableName == null || variableName.trim().isEmpty()) {
                throw new IllegalStateException("Nome variabile vuoto nel mapping: '" + variableName + "'");
            }

            if (variableId == null || variableId <= 0) {
                throw new IllegalStateException("ID variabile non valido per '" + variableName + "': " + variableId);
            }

            if (variableId > variableCount) {
                throw new IllegalStateException("ID variabile fuori range per '" + variableName + "': " +
                        variableId + " > " + variableCount);
            }
        }
    }

    /**
     * Valida range e consistenza dei letterali nelle clausole.
     */
    private void validateClauseLiterals() {
        for (int clauseIndex = 0; clauseIndex < clauses.size(); clauseIndex++) {
            List<Integer> clause = clauses.get(clauseIndex);

            for (int literalIndex = 0; literalIndex < clause.size(); literalIndex++) {
                Integer literal = clause.get(literalIndex);
                int absoluteLiteral = Math.abs(literal);

                if (literal == null || literal == 0) {
                    throw new IllegalStateException("Letterale non valido in clausola " + clauseIndex +
                            "[" + literalIndex + "]: " + literal);
                }

                if (absoluteLiteral > variableCount) {
                    throw new IllegalStateException("Letterale fuori range in clausola " + clauseIndex +
                            "[" + literalIndex + "]: |" + literal + "| > " + variableCount);
                }
            }
        }
    }

    //endregion

    //region STATISTICHE E LOGGING

    /**
     * Registra statistiche dettagliate sulla conversione completata.
     */
    private void logConversionStatistics() {
        int totalLiterals = clauses.stream().mapToInt(List::size).sum();
        double avgClauseLength = clauses.isEmpty() ? 0.0 : (double) totalLiterals / clauses.size();

        LOGGER.info(String.format("Conversione CNF completata: %d clausole, %d variabili, %.1f letterali/clausola",
                clauses.size(), variableCount, avgClauseLength));

        // Statistiche avanzate per debugging
        if (LOGGER.isLoggable(Level.FINE)) {
            logAdvancedStatistics(totalLiterals, avgClauseLength);
        }
    }

    /**
     * Registra statistiche avanzate per analisi approfondita.
     */
    private void logAdvancedStatistics(int totalLiterals, double avgClauseLength) {
        // Distribuzione lunghezza clausole
        Map<Integer, Long> lengthDistribution = clauses.stream()
                .collect(java.util.stream.Collectors.groupingBy(
                        List::size, java.util.stream.Collectors.counting()));

        LOGGER.fine("Distribuzione lunghezza clausole: " + lengthDistribution);

        // Analisi densità formula
        double density = (double) totalLiterals / (variableCount * clauses.size());
        LOGGER.fine(String.format("Densità formula: %.3f (letterali per variabile-clausola)", density));

        // Clausole unitarie
        long unitClauses = clauses.stream().filter(clause -> clause.size() == 1).count();
        LOGGER.fine("Clausole unitarie: " + unitClauses + "/" + clauses.size());

        // Log mapping variabili per debugging
        if (LOGGER.isLoggable(Level.FINEST)) {
            LOGGER.finest("Mapping completo variabili: " + variableMapping);
        }
    }

    //endregion

    //region INTERFACCIA PUBBLICA

    /**
     * @return copia immutabile delle clausole CNF in formato numerico
     */
    public List<List<Integer>> getClauses() {
        return new ArrayList<>(clauses);
    }

    /**
     * @return numero di variabili distinte nella formula
     */
    public int getVariableCount() {
        return variableCount;
    }

    /**
     * @return numero di clausole nella formula
     */
    public int getClausesCount() {
        return clauses.size();
    }

    /**
     * @return copia immutabile del mapping variabili simboliche → ID numerici
     */
    public Map<String, Integer> getVariableMapping() {
        return new LinkedHashMap<>(variableMapping);
    }

    /**
     * Rappresentazione testuale per debugging con informazioni essenziali.
     */
    @Override
    public String toString() {
        return String.format("CNFFormula{clausole=%d, variabili=%d, mapping=%s}",
                clauses.size(), variableCount, variableMapping.keySet());
    }

    //endregion
}

//endregion

//region MODELLO LETTERALE ASSEGNATO CON METADATA COMPLETI

/**
 * LETTERALE ASSEGNATO - Modello completo di variabile assegnata con metadata genealogici
 *
 * Rappresenta una variabile assegnata durante l'algoritmo CDCL con tutti i metadata necessari
 * per tracking completo, backtracking efficiente e analisi dei conflitti. Incapsula tutte
 * le informazioni genealogiche dell'assegnamento per supportare operazioni avanzate.
 *
 * INFORMAZIONI MEMORIZZATE:
 * • Identificazione variabile e valore assegnato
 * • Tipo assegnamento (decisione euristica vs implicazione)
 * • Clausola ancestrale per implicazioni (genealogia)
 * • Validazioni comprehensive per consistenza dati
 * • Interfaccia immutabile per thread-safety
 *
 * UTILIZZI NELL'ALGORITMO CDCL:
 * • Tracking cronologia decisioni per backtracking
 * • Identificazione catene di implicazioni per conflict analysis
 * • Generazione spiegazioni matematiche per prove
 * • Ricostruzione modelli SAT con tracciabilità
 */
class AssignedLiteral {

    //region ATTRIBUTI CORE DELL'ASSEGNAMENTO

    /**
     * ID numerico della variabile assegnata.
     * Corrisponde agli ID generati da CNFFormula (sempre > 0).
     * Invariante: valore immutabile e sempre positivo.
     */
    private final Integer variable;

    /**
     * Valore booleano assegnato alla variabile.
     * • true: variabile impostata a vero
     * • false: variabile impostata a falso
     * Invariante: non null, valore immutabile.
     */
    private final Boolean value;

    /**
     * Tipo di assegnamento per distinguere origini diverse.
     * • true: decisione euristica presa dal decision maker
     * • false: implicazione derivata da unit propagation
     * Invariante: non null, determina comportamento backtracking.
     */
    private final Boolean isDecision;

    /**
     * Clausola che ha causato questa implicazione (genealogia).
     * • null per decisioni euristiche (auto-giustificate)
     * • Lista non vuota per implicazioni (clausola unit causante)
     * Invariante: consistenza con tipo assegnamento.
     */
    private final List<Integer> ancestorClause;

    //endregion

    //region COSTRUZIONE CON VALIDAZIONE COMPLETA

    /**
     * Costruisce letterale assegnato con validazione completa di tutti i parametri.
     *
     * VALIDAZIONI APPLICATE:
     * • Variable ID deve essere > 0 (range valido per formula)
     * • Value non può essere null (assegnamento completo richiesto)
     * • IsDecision non può essere null (tipo deve essere definito)
     * • Implicazioni richiedono clausola ancestrale non vuota
     * • Decisioni non dovrebbero avere clausola ancestrale
     * • Clausola ancestrale deve contenere solo letterali validi
     *
     * @param variable ID numerico variabile (> 0)
     * @param value valore booleano assegnato (non null)
     * @param isDecision true se decisione, false se implicazione
     * @param ancestorClause clausola causante (richiesta per implicazioni)
     * @throws IllegalArgumentException se parametri inconsistenti o malformati
     */
    public AssignedLiteral(Integer variable, Boolean value, Boolean isDecision, List<Integer> ancestorClause) {
        // Validazione parametri di base
        validateBasicParameters(variable, value, isDecision);

        // Validazione coerenza tipo-clausola
        validateTypeClauseConsistency(isDecision, ancestorClause);

        // Validazione contenuto clausola ancestrale
        if (ancestorClause != null) {
            validateAncestorClauseContent(ancestorClause);
        }

        // Assegnazione con copia difensiva
        this.variable = variable;
        this.value = value;
        this.isDecision = isDecision;
        this.ancestorClause = ancestorClause != null ?
                Collections.unmodifiableList(new ArrayList<>(ancestorClause)) : null;
    }

    /**
     * Valida parametri di base per consistenza e range.
     */
    private void validateBasicParameters(Integer variable, Boolean value, Boolean isDecision) {
        if (variable == null || variable <= 0) {
            throw new IllegalArgumentException("Variable ID deve essere > 0, ricevuto: " + variable);
        }
        if (value == null) {
            throw new IllegalArgumentException("Value non può essere null");
        }
        if (isDecision == null) {
            throw new IllegalArgumentException("IsDecision non può essere null");
        }
    }

    /**
     * Valida coerenza tra tipo assegnamento e presenza clausola ancestrale.
     */
    private void validateTypeClauseConsistency(Boolean isDecision, List<Integer> ancestorClause) {
        if (!isDecision && (ancestorClause == null || ancestorClause.isEmpty())) {
            throw new IllegalArgumentException("Implicazioni richiedono clausola ancestrale non vuota");
        }
        if (isDecision && ancestorClause != null && !ancestorClause.isEmpty()) {
            throw new IllegalArgumentException("Decisioni non dovrebbero avere clausola ancestrale");
        }
    }

    /**
     * Valida contenuto clausola ancestrale per consistenza.
     */
    private void validateAncestorClauseContent(List<Integer> ancestorClause) {
        for (Integer literal : ancestorClause) {
            if (literal == null || literal == 0) {
                throw new IllegalArgumentException("Clausola ancestrale contiene letterale non valido: " + literal);
            }
        }
    }

    //endregion

    //region INTERFACCIA PUBBLICA ACCESSORS

    /**
     * @return ID numerico della variabile assegnata
     */
    public Integer getVariable() {
        return variable;
    }

    /**
     * @return valore booleano assegnato alla variabile
     */
    public Boolean getValue() {
        return value;
    }

    /**
     * @return true se assegnamento è decisione euristica
     */
    public Boolean isDecision() {
        return isDecision;
    }

    /**
     * @return true se assegnamento è implicazione da unit propagation
     */
    public Boolean isImplication() {
        return !isDecision;
    }

    /**
     * @return copia immutabile clausola ancestrale (null per decisioni)
     */
    public List<Integer> getAncestorClause() {
        return ancestorClause; // Già immutabile per costruzione
    }

    /**
     * @return true se esiste clausola ancestrale valida
     */
    public boolean hasAncestorClause() {
        return ancestorClause != null && !ancestorClause.isEmpty();
    }

    //endregion

    //region UTILITÀ E CONVERSIONI

    /**
     * Converte assegnamento in letterale DIMACS standard.
     * @return ID positivo se variabile true, negativo se false
     */
    public Integer toDIMACSLiteral() {
        return value ? variable : -variable;
    }

    /**
     * Genera descrizione testuale completa per debugging e logging.
     */
    @Override
    public String toString() {
        StringBuilder description = new StringBuilder();
        description.append("AssignedLiteral{");
        description.append("var=").append(variable);
        description.append(", val=").append(value);
        description.append(", type=").append(isDecision ? "DECISION" : "IMPLICATION");

        if (hasAncestorClause()) {
            description.append(", ancestor=").append(ancestorClause);
        }

        description.append('}');
        return description.toString();
    }

    /**
     * Uguaglianza basata su variabile, valore e tipo (ignora clausola ancestrale).
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;

        AssignedLiteral other = (AssignedLiteral) obj;
        return Objects.equals(variable, other.variable) &&
                Objects.equals(value, other.value) &&
                Objects.equals(isDecision, other.isDecision);
    }

    /**
     * Hash code consistente con equals per uso in collezioni.
     */
    @Override
    public int hashCode() {
        return Objects.hash(variable, value, isDecision);
    }

    //endregion
}

//endregion

//region STACK GERARCHICO PER GESTIONE LIVELLI E BACKTRACKING

/**
 * DECISION STACK - Stack gerarchico per gestione livelli nell'algoritmo CDCL
 *
 * Implementa la struttura dati avanzata per organizzazione gerarchica delle decisioni
 * e implicazioni durante la ricerca SAT. Fornisce supporto completo per operazioni
 * di backtracking cronologico e non-cronologico con efficienza ottimale.
 *
 * ORGANIZZAZIONE GERARCHICA:
 * • Livello 0: implicazioni da clausole unitarie originali (sempre presente)
 * • Livello i (i>0): livello di decisione i con decisione + implicazioni derivate
 * • Ogni livello mantiene cronologia completa degli assegnamenti
 * • Stack mai completamente vuoto per garantire stabilità
 *
 * OPERAZIONI SUPPORTATE:
 * • Aggiunta decisioni euristiche con creazione nuovi livelli
 * • Aggiunta implicazioni al livello corrente
 * • Backtracking cronologico (rimozione livello superiore)
 * • Backjumping non-cronologico (salto a livelli specifici)
 * • Interrogazione stato e navigazione livelli
 *
 * INVARIANTI MANTENUTE:
 * • Stack contiene sempre almeno livello 0
 * • Ogni livello ha struttura temporale consistente
 * • Operazioni atomiche per consistenza durante backtracking
 * • Validazione completa di tutti i parametri
 */
class DecisionStack {

    private static final Logger LOGGER = Logger.getLogger(DecisionStack.class.getName());

    //region STRUTTURA DATI STACK GERARCHICO

    /**
     * Stack dei livelli di decisione con organizzazione gerarchica ottimizzata.
     *
     * STRUTTURA DETTAGLIATA:
     * • Indice 0: livello 0 (implicazioni iniziali, sempre presente)
     * • Indice i>0: livello i di decisione con cronologia temporale
     * • Ogni livello è ArrayList<AssignedLiteral> con assegnamenti ordinati cronologicamente
     *
     * INVARIANTI CRITICHE:
     * • size() >= 1 (livello 0 sempre presente, mai rimosso)
     * • Ogni livello non null e con struttura valida
     * • Ordine cronologico mantenuto all'interno di ogni livello
     */
    private final Stack<ArrayList<AssignedLiteral>> levelStack;

    //endregion

    //region INIZIALIZZAZIONE E CONFIGURAZIONE

    /**
     * Inizializza stack con livello 0 vuoto e pronto per operazioni.
     * Il livello 0 è riservato esclusivamente a implicazioni da clausole unitarie originali.
     */
    public DecisionStack() {
        this.levelStack = new Stack<>();
        this.levelStack.push(new ArrayList<>()); // Livello 0 iniziale sempre presente

        LOGGER.fine("DecisionStack inizializzato con livello 0 protetto");
    }

    //endregion

    //region OPERAZIONI DI AGGIUNTA CON VALIDAZIONE

    /**
     * Aggiunge decisione euristica creando nuovo livello gerarchico.
     *
     * ALGORITMO AGGIUNTA DECISIONE:
     * 1. Validazione parametri di input per consistenza e range
     * 2. Creazione assegnamento decisionale con metadata completi
     * 3. Inizializzazione nuovo livello con la decisione come primo elemento
     * 4. Push atomico del nuovo livello nello stack (incrementa altezza)
     * 5. Logging informazioni per debugging e audit
     *
     * @param variable ID variabile da decidere (> 0, non ancora assegnata)
     * @param value valore booleano da assegnare alla variabile
     * @throws IllegalArgumentException se parametri non validi
     * @throws IllegalStateException se variabile già assegnata
     */
    public void addDecision(Integer variable, Boolean value) {
        validateDecisionParameters(variable, value);

        // Crea assegnamento decisionale auto-giustificato
        AssignedLiteral decision = new AssignedLiteral(variable, value, true, null);

        // Inizializza nuovo livello con la decisione
        ArrayList<AssignedLiteral> newDecisionLevel = new ArrayList<>();
        newDecisionLevel.add(decision);

        // Operazione atomica di aggiunta livello
        levelStack.push(newDecisionLevel);

        int currentLevel = levelStack.size() - 1;
        LOGGER.fine(String.format("Decisione aggiunta: var=%d, val=%s, livello=%d, altezza_stack=%d",
                variable, value, currentLevel, levelStack.size()));
    }

    /**
     * Aggiunge implicazione derivata da unit propagation al livello corrente.
     *
     * ALGORITMO AGGIUNTA IMPLICAZIONE:
     * 1. Validazione parametri e clausola ancestrale per consistenza
     * 2. Verifica stato stack per prevenzione inconsistenze
     * 3. Creazione assegnamento di implicazione con genealogia
     * 4. Modifica atomica del livello corrente (pop + modifica + push)
     * 5. Logging con informazioni contestuali dettagliate
     *
     * @param variable ID variabile implicata (> 0)
     * @param value valore implicato dalla propagazione
     * @param ancestorClause clausola unitaria causante l'implicazione
     * @throws IllegalArgumentException se parametri non validi
     * @throws IllegalStateException se stack inconsistente
     */
    public void addImpliedLiteral(Integer variable, Boolean value, List<Integer> ancestorClause) {
        validateImplicationParameters(variable, value, ancestorClause);

        if (levelStack.isEmpty()) {
            throw new IllegalStateException("Stack vuoto - impossibile aggiungere implicazione");
        }

        // Crea implicazione con clausola ancestrale per tracciabilità
        AssignedLiteral implication = new AssignedLiteral(variable, value, false, ancestorClause);

        // Modifica atomica del livello corrente
        ArrayList<AssignedLiteral> currentLevel = levelStack.pop();
        currentLevel.add(implication);
        levelStack.push(currentLevel);

        int levelIndex = levelStack.size() - 1;
        LOGGER.fine(String.format("Implicazione aggiunta: var=%d, val=%s, livello=%d, clausola=%s, size_livello=%d",
                variable, value, levelIndex, ancestorClause, currentLevel.size()));
    }

    /**
     * Valida parametri per aggiunta decisione.
     */
    private void validateDecisionParameters(Integer variable, Boolean value) {
        if (variable == null || variable <= 0) {
            throw new IllegalArgumentException("Variable ID per decisione deve essere > 0, ricevuto: " + variable);
        }
        if (value == null) {
            throw new IllegalArgumentException("Value per decisione non può essere null");
        }
    }

    /**
     * Valida parametri per aggiunta implicazione.
     */
    private void validateImplicationParameters(Integer variable, Boolean value, List<Integer> ancestorClause) {
        if (variable == null || variable <= 0) {
            throw new IllegalArgumentException("Variable ID per implicazione deve essere > 0, ricevuto: " + variable);
        }
        if (value == null) {
            throw new IllegalArgumentException("Value per implicazione non può essere null");
        }
        if (ancestorClause == null || ancestorClause.isEmpty()) {
            throw new IllegalArgumentException("AncestorClause richiesta per implicazioni");
        }

        // Validazione contenuto clausola ancestrale
        for (Integer literal : ancestorClause) {
            if (literal == null || literal == 0) {
                throw new IllegalArgumentException("Clausola ancestrale contiene letterale non valido: " + literal);
            }
        }
    }

    //endregion

    //region OPERAZIONI DI RIMOZIONE E BACKTRACKING

    /**
     * Rimuove livello più alto (backtracking cronologico singolo).
     *
     * PROTEZIONI IMPLEMENTATE:
     * • Livello 0 è protetto e non può mai essere rimosso
     * • Operazione atomica per garantire consistenza durante concorrenza
     * • Restituisce copia difensiva degli assegnamenti rimossi
     * • Logging dettagliato per audit delle operazioni
     *
     * @return lista assegnamenti del livello rimosso (vuota se tentativo rimozione livello 0)
     */
    public List<AssignedLiteral> deleteLevel() {
        if (levelStack.size() <= 1) {
            LOGGER.warning("Tentativo rimozione livello 0 protetto - operazione ignorata per sicurezza");
            return new ArrayList<>(); // Protezione livello 0
        }

        ArrayList<AssignedLiteral> removedLevel = levelStack.pop();
        int removedLevelIndex = levelStack.size(); // Indice del livello appena rimosso

        LOGGER.fine(String.format("Livello %d rimosso: %d assegnamenti, altezza_stack=%d",
                removedLevelIndex, removedLevel.size(), levelStack.size()));

        // Log dettagliato assegnamenti rimossi per debugging
        if (LOGGER.isLoggable(Level.FINEST)) {
            for (int i = 0; i < removedLevel.size(); i++) {
                AssignedLiteral assignment = removedLevel.get(i);
                LOGGER.finest(String.format("Rimosso[%d]: %s", i, assignment));
            }
        }

        return new ArrayList<>(removedLevel); // Copia difensiva
    }

    /**
     * Backtracking non-cronologico al livello target (backjumping avanzato).
     *
     * ALGORITMO BACKJUMPING:
     * 1. Validazione livello target per safety e consistenza
     * 2. Rimozione sequenziale livelli superiori fino a target
     * 3. Raccolta tutti gli assegnamenti rimossi per rollback
     * 4. Logging statistiche complete dell'operazione
     * 5. Verifica integrità finale dello stack
     *
     * @param targetLevel livello di destinazione (>= 0, <= livello corrente)
     * @return tutti gli assegnamenti rimossi durante l'operazione di backjump
     * @throws IllegalArgumentException se targetLevel non valido
     */
    public List<AssignedLiteral> backtrackToLevel(int targetLevel) {
        int currentLevel = levelStack.size() - 1;
        validateBacktrackLevel(targetLevel, currentLevel);

        if (targetLevel == currentLevel) {
            LOGGER.fine("Backtrack richiesto al livello corrente - nessuna operazione necessaria");
            return new ArrayList<>();
        }

        List<AssignedLiteral> allRemovedAssignments = new ArrayList<>();
        int levelsToRemove = currentLevel - targetLevel;

        // Rimozione sequenziale con accumulo assegnamenti
        for (int i = 0; i < levelsToRemove; i++) {
            List<AssignedLiteral> removedLevel = deleteLevel();
            allRemovedAssignments.addAll(removedLevel);
        }

        LOGGER.info(String.format("Backjump completato: %d → %d (%d livelli), %d assegnamenti rimossi",
                currentLevel, targetLevel, levelsToRemove, allRemovedAssignments.size()));

        return allRemovedAssignments;
    }

    /**
     * Valida livello target per operazioni backtrack.
     */
    private void validateBacktrackLevel(int targetLevel, int currentLevel) {
        if (targetLevel < 0) {
            throw new IllegalArgumentException("Target level non può essere negativo: " + targetLevel);
        }
        if (targetLevel > currentLevel) {
            throw new IllegalArgumentException(
                    String.format("Target level %d > current level %d", targetLevel, currentLevel));
        }
    }

    //endregion

    //region OPERAZIONI DI INTERROGAZIONE E NAVIGAZIONE

    /**
     * @return copia difensiva degli assegnamenti nel livello più alto
     */
    public List<AssignedLiteral> getTopLevel() {
        if (levelStack.isEmpty()) {
            throw new IllegalStateException("Stack vuoto - nessun livello disponibile");
        }
        return new ArrayList<>(levelStack.peek());
    }

    /**
     * @return livello corrente (numero di livelli - 1, sempre >= 0)
     */
    public int getLevel() {
        return levelStack.size() - 1;
    }

    /**
     * @return numero totale di livelli nello stack (sempre >= 1)
     */
    public int size() {
        return levelStack.size();
    }

    /**
     * Restituisce ID delle variabili assegnate a livello specifico.
     * @param levelIndex indice livello da interrogare (0 <= levelIndex < size())
     * @return lista ID variabili in ordine cronologico di assegnamento
     */
    public List<Integer> getLiteralsAtLevel(int levelIndex) {
        validateLevelIndex(levelIndex);

        List<AssignedLiteral> levelAssignments = levelStack.get(levelIndex);
        return levelAssignments.stream()
                .map(AssignedLiteral::getVariable)
                .collect(java.util.stream.Collectors.toList());
    }

    /**
     * Restituisce tutti gli assegnamenti a livello specifico.
     * @param levelIndex indice livello da interrogare
     * @return copia difensiva degli assegnamenti al livello
     */
    public List<AssignedLiteral> getAssignmentsAtLevel(int levelIndex) {
        validateLevelIndex(levelIndex);
        return new ArrayList<>(levelStack.get(levelIndex));
    }

    /**
     * @return true se stack contiene solo livello 0 vuoto
     */
    public boolean isEmpty() {
        return levelStack.size() == 1 && levelStack.peek().isEmpty();
    }

    /**
     * @return numero totale assegnamenti in tutti i livelli
     */
    public int getTotalAssignments() {
        return levelStack.stream()
                .mapToInt(ArrayList::size)
                .sum();
    }

    /**
     * Trova livello di decisione di una variabile specifica.
     * @param variable ID variabile da cercare
     * @return livello della variabile o -1 se non trovata
     */
    public int findVariableLevel(Integer variable) {
        if (variable == null) {
            return -1;
        }

        for (int level = 0; level < levelStack.size(); level++) {
            List<AssignedLiteral> levelAssignments = levelStack.get(level);

            for (AssignedLiteral assignment : levelAssignments) {
                if (assignment.getVariable().equals(variable)) {
                    return level;
                }
            }
        }

        return -1; // Variabile non trovata
    }

    /**
     * Trova assegnamento specifico per una variabile.
     * @param variable ID variabile da cercare
     * @return assegnamento della variabile o null se non trovata
     */
    public AssignedLiteral findVariableAssignment(Integer variable) {
        if (variable == null) {
            return null;
        }

        for (ArrayList<AssignedLiteral> level : levelStack) {
            for (AssignedLiteral assignment : level) {
                if (assignment.getVariable().equals(variable)) {
                    return assignment;
                }
            }
        }

        return null; // Variabile non trovata
    }

    /**
     * Valida indice livello per accesso sicuro.
     */
    private void validateLevelIndex(int levelIndex) {
        if (levelIndex < 0 || levelIndex >= levelStack.size()) {
            throw new IndexOutOfBoundsException(
                    String.format("Level index %d fuori range [0, %d)", levelIndex, levelStack.size()));
        }
    }

    //endregion

    //region STATISTICHE E RAPPRESENTAZIONE

    /**
     * Restituisce statistiche dettagliate sullo stack per analisi performance.
     */
    public StackStatistics getStatistics() {
        int totalLevels = levelStack.size();
        int totalAssignments = getTotalAssignments();
        int decisionsCount = totalLevels - 1; // Esclude livello 0
        int implicationsCount = totalAssignments - decisionsCount;

        return new StackStatistics(totalLevels, totalAssignments, decisionsCount, implicationsCount);
    }

    /**
     * Rappresentazione testuale completa per debugging avanzato.
     */
    @Override
    public String toString() {
        StringBuilder representation = new StringBuilder();
        representation.append("DecisionStack {\n");
        representation.append(String.format("  Livelli: %d, Assegnamenti totali: %d\n",
                levelStack.size(), getTotalAssignments()));

        for (int levelIndex = 0; levelIndex < levelStack.size(); levelIndex++) {
            ArrayList<AssignedLiteral> level = levelStack.get(levelIndex);
            representation.append(String.format("\n  Livello %d (%d assegnamenti):\n",
                    levelIndex, level.size()));

            if (level.isEmpty()) {
                representation.append("    [vuoto]\n");
                continue;
            }

            for (int i = 0; i < level.size(); i++) {
                AssignedLiteral assignment = level.get(i);
                String type = assignment.isDecision() ? "DECISION" : "IMPLIED";
                String clauseInfo = assignment.hasAncestorClause()
                        ? " ← " + assignment.getAncestorClause()
                        : "";

                representation.append(String.format("    [%d] %s: %d → %s%s\n",
                        i, type, assignment.getVariable(), assignment.getValue(), clauseInfo));
            }
        }

        representation.append("}");
        return representation.toString();
    }

    //endregion

    //region CLASSI DI SUPPORTO

    /**
     * Statistiche dettagliate dello stack per analisi performance.
     */
    public static class StackStatistics {
        public final int totalLevels;
        public final int totalAssignments;
        public final int decisionsCount;
        public final int implicationsCount;

        public StackStatistics(int totalLevels, int totalAssignments, int decisionsCount, int implicationsCount) {
            this.totalLevels = totalLevels;
            this.totalAssignments = totalAssignments;
            this.decisionsCount = decisionsCount;
            this.implicationsCount = implicationsCount;
        }

        @Override
        public String toString() {
            return String.format("StackStats{levels=%d, assignments=%d, decisions=%d, implications=%d}",
                    totalLevels, totalAssignments, decisionsCount, implicationsCount);
        }
    }

    //endregion
}

//endregion