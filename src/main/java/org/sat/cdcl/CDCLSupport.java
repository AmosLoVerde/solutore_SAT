package org.sat.cdcl;

import org.sat.cnf.CNFConverter;
import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;


//region RAPPRESENTAZIONE FORMULA CNF OTTIMIZZATA

/**
 * Converte la rappresentazione ad albero CNFConverter in una struttura dati
 * ottimizzata per l'algoritmo CDCL. Si utilizzano identificatori numerici
 * per le variabili e rappresentazioni compatte per le clausole.
 */
class CNFFormula {

    private static final Logger LOGGER = Logger.getLogger(CNFFormula.class.getName());

    //region STRUTTURE DATI PRINCIPALI

    /**
     * Clausole della formula CNF in formato ottimizzato.
     * Ogni clausola è List<Integer> dove ogni Integer è un letterale.
     * Invariante: lista immutabile dopo costruzione
     */
    private final List<List<Integer>> clauses;

    /**
     * Numero totale di variabili distinte nella formula.
     * Corrisponde al massimo ID variabile assegnato.
     */
    private final int variableCount;

    /**
     * Mapping bidirezionale: nome simbolico → ID numerico.
     * Mantiene tracciabilità per debugging e generazione output.
     * Invariante: ogni nome ha ID univoco ≥ 1
     */
    private final Map<String, Integer> variableMapping;

    //endregion


    //region COSTRUZIONE E CONVERSIONE

    /**
     * Costruisce formula CNF ottimizzata da rappresentazione ad albero.
     *
     * @param cnfConverter formula CNF in formato albero
     * @throws IllegalArgumentException se formula malformata
     * @throws RuntimeException se errori durante conversione
     */
    public CNFFormula(CNFConverter cnfConverter) {
        if (cnfConverter == null) {
            throw new IllegalArgumentException("CNFConverter non può essere null");
        }

        LOGGER.info("=== CONVERSIONE FORMULA CNF ===");

        // Inizializzazione strutture dati
        this.clauses = new ArrayList<>();
        this.variableMapping = new LinkedHashMap<>(); // Mantiene ordine inserimento

        try {
            // Conversione principale
            performConversionFromTree(cnfConverter);

            // Finalizzazione
            this.variableCount = variableMapping.size();
            validateConversionIntegrity();
            logConversionStatistics();

        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Errore conversione CNF", e);
            throw new RuntimeException("Conversione CNF fallita: " + e.getMessage(), e);
        }

        LOGGER.info("=== CONVERSIONE CNF COMPLETATA ===");
    }

    /**
     * Esegue la conversione principale dall'albero CNFConverter.
     * Gestisce sia formule complesse (AND di clausole) che semplici (clausola singola).
     */
    private void performConversionFromTree(CNFConverter converter) {
        LOGGER.fine("Conversione da tipo: " + converter.type);

        switch (converter.type) {
            case AND:
                // Formula complessa: congiunzione di clausole multiple
                processConjunctionOfClauses(converter);
                break;

            default:
                // Formula semplice: clausola singola o letterale
                processSingleClause(converter);
                break;
        }

        LOGGER.fine("Clausole estratte: " + clauses.size());
    }

    /**
     * Processa congiunzione di clausole (nodo AND con operandi multipli).
     * Ogni operando rappresenta una clausola da convertire separatamente.
     */
    private void processConjunctionOfClauses(CNFConverter conjunctionNode) {
        if (conjunctionNode.operands == null || conjunctionNode.operands.isEmpty()) {
            LOGGER.warning("Nodo AND vuoto - formula senza clausole");
            return;
        }

        LOGGER.fine("Processando " + conjunctionNode.operands.size() + " clausole");

        for (CNFConverter clauseNode : conjunctionNode.operands) {
            List<Integer> convertedClause = convertSingleClause(clauseNode);
            if (isValidClause(convertedClause)) {
                clauses.add(convertedClause);
                LOGGER.finest("Clausola aggiunta: " + convertedClause);
            }
        }
    }

    /**
     * Processa clausola singola (letterale o disgiunzione).
     */
    private void processSingleClause(CNFConverter singleNode) {
        List<Integer> convertedClause = convertSingleClause(singleNode);
        if (isValidClause(convertedClause)) {
            clauses.add(convertedClause);
            LOGGER.fine("Clausola singola aggiunta: " + convertedClause);
        }
    }

    //endregion


    //region CONVERSIONE CLAUSOLE E LETTERALI

    /**
     * Converte una singola clausola da nodo albero a rappresentazione numerica.
     *
     * TIPI GESTITI:
     * - OR: disgiunzione di letterali → clausola normale
     * - ATOM: variabile atomica → clausola unitaria positiva
     * - NOT: negazione variabile → clausola unitaria negativa
     *
     * @param clauseNode nodo rappresentante la clausola
     * @return lista letterali convertiti (vuota se conversione fallisce)
     */
    private List<Integer> convertSingleClause(CNFConverter clauseNode) {
        List<Integer> literals = new ArrayList<>();

        switch (clauseNode.type) {
            case OR:
                // Clausola normale: disgiunzione di letterali
                literals = convertDisjunctionToLiterals(clauseNode);
                break;

            case ATOM:
            case NOT:
                // Clausola unitaria: singolo letterale
                Integer literal = convertSingleLiteral(clauseNode);
                if (literal != null) {
                    literals.add(literal);
                }
                break;

            default:
                LOGGER.warning("Tipo clausola non supportato: " + clauseNode.type);
                break;
        }

        return literals;
    }

    /**
     * Converte nodo OR (disgiunzione) in lista di letterali.
     * Ogni operando del nodo OR diventa un letterale nella clausola risultante.
     */
    private List<Integer> convertDisjunctionToLiterals(CNFConverter orNode) {
        List<Integer> literals = new ArrayList<>();

        if (orNode.operands == null) {
            LOGGER.warning("Nodo OR senza operandi");
            return literals;
        }

        LOGGER.finest("Convertendo " + orNode.operands.size() + " letterali");

        for (CNFConverter literalNode : orNode.operands) {
            Integer convertedLiteral = convertSingleLiteral(literalNode);
            if (convertedLiteral != null) {
                literals.add(convertedLiteral);
            }
        }

        return literals;
    }

    /**
     * Converte un singolo letterale in rappresentazione numerica.
     *
     * CONVERSIONE:
     * - ATOM "P" → +ID (letterale positivo)
     * - NOT ATOM "¬P" → -ID (letterale negativo)
     *
     * @param literalNode nodo rappresentante il letterale
     * @return ID numerico del letterale (null se non convertibile)
     */
    private Integer convertSingleLiteral(CNFConverter literalNode) {
        switch (literalNode.type) {
            case ATOM:
                return convertPositiveLiteral(literalNode);

            case NOT:
                return convertNegativeLiteral(literalNode);

            default:
                LOGGER.warning("Tipo letterale non riconosciuto: " + literalNode.type);
                return null;
        }
    }

    /**
     * Converte letterale positivo (variabile atomica).
     * Estrae nome variabile e assegna/recupera ID numerico.
     */
    private Integer convertPositiveLiteral(CNFConverter atomNode) {
        String variableName = extractVariableName(atomNode.atom);
        if (variableName == null) return null;

        Integer variableId = getOrCreateVariableId(variableName);
        LOGGER.finest("Letterale positivo: " + variableName + " → " + variableId);
        return variableId;
    }

    /**
     * Converte letterale negativo (NOT di variabile atomica).
     * Verifica struttura NOT(ATOM) e restituisce ID negativo.
     */
    private Integer convertNegativeLiteral(CNFConverter notNode) {
        // Validazione struttura NOT(ATOM)
        if (notNode.operand == null || notNode.operand.type != CNFConverter.Type.ATOM) {
            LOGGER.warning("Struttura NOT non valida");
            return null;
        }

        String variableName = extractVariableName(notNode.operand.atom);
        if (variableName == null) return null;

        Integer variableId = getOrCreateVariableId(variableName);
        Integer negatedId = -variableId;

        LOGGER.finest("Letterale negativo: ¬" + variableName + " → " + negatedId);
        return negatedId;
    }

    //endregion


    //region GESTIONE MAPPING VARIABILI

    /**
     * Estrae e valida nome variabile da stringa atomica.
     * Rimuove spazi e verifica che non sia vuota.
     */
    private String extractVariableName(String atom) {
        if (atom == null || atom.trim().isEmpty()) {
            LOGGER.warning("Nome variabile vuoto o null");
            return null;
        }
        return atom.trim();
    }

    /**
     * Ottiene ID numerico per variabile, creandolo se necessario.
     * Implementa mapping lazy con assegnazione progressiva.
     *
     * ALGORITMO:
     * 1. Se variabile già mappata → restituisce ID esistente
     * 2. Se variabile nuova → assegna prossimo ID disponibile
     * 3. Aggiorna mapping e registra nel log
     *
     * @param variableName nome simbolico della variabile
     * @return ID numerico univoco (sempre > 0)
     */
    private Integer getOrCreateVariableId(String variableName) {
        return variableMapping.computeIfAbsent(variableName, name -> {
            int newId = variableMapping.size() + 1;
            LOGGER.finest("Nuova variabile: " + name + " → " + newId);
            return newId;
        });
    }

    //endregion


    //region VALIDAZIONE E STATISTICHE

    /**
     * Verifica se una clausola convertita è valida per inclusione.
     */
    private boolean isValidClause(List<Integer> clause) {
        return clause != null && !clause.isEmpty();
    }

    /**
     * Valida integrità della conversione completata.
     * Verifica consistenza tra strutture dati e assenza di corruzioni.
     */
    private void validateConversionIntegrity() {
        // Verifica coerenza conteggio variabili
        if (variableCount != variableMapping.size()) {
            throw new IllegalStateException("Inconsistenza conteggio variabili");
        }

        // Verifica integrità mapping
        for (Map.Entry<String, Integer> entry : variableMapping.entrySet()) {
            if (entry.getKey() == null || entry.getKey().trim().isEmpty()) {
                throw new IllegalStateException("Nome variabile vuoto nel mapping");
            }
            if (entry.getValue() == null || entry.getValue() <= 0) {
                throw new IllegalStateException("ID variabile non valido: " + entry.getValue());
            }
        }

        // Verifica range letterali nelle clausole
        for (List<Integer> clause : clauses) {
            for (Integer literal : clause) {
                int absLiteral = Math.abs(literal);
                if (absLiteral <= 0 || absLiteral > variableCount) {
                    throw new IllegalStateException("Letterale fuori range: " + literal);
                }
            }
        }

        LOGGER.fine("Validazione conversione: SUCCESSO");
    }

    /**
     * Registra statistiche dettagliate sulla conversione completata.
     */
    private void logConversionStatistics() {
        int totalLiterals = clauses.stream().mapToInt(List::size).sum();
        double avgClauseLength = clauses.isEmpty() ? 0.0 : (double) totalLiterals / clauses.size();

        LOGGER.info(String.format("Formula convertita: %d clausole, %d variabili, %.1f letterali/clausola",
                clauses.size(), variableCount, avgClauseLength));

        // Log dettagliato per debugging
        if (LOGGER.isLoggable(Level.FINEST)) {
            LOGGER.finest("Mapping variabili: " + variableMapping);

            Map<Integer, Long> lengthDistribution = clauses.stream()
                    .collect(java.util.stream.Collectors.groupingBy(
                            List::size, java.util.stream.Collectors.counting()));
            LOGGER.finest("Distribuzione lunghezza clausole: " + lengthDistribution);
        }
    }

    //endregion


    //region INTERFACCIA PUBBLICA

    /**
     * @return copia immutabile delle clausole CNF
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
     * @return copia immutabile del mapping variabili
     */
    public Map<String, Integer> getVariableMapping() {
        return new LinkedHashMap<>(variableMapping);
    }

    @Override
    public String toString() {
        return String.format("CNFFormula{clausole=%d, variabili=%d, mapping=%s}",
                clauses.size(), variableCount, variableMapping);
    }

    //endregion
}

//endregion


//region MODELLO LETTERALE ASSEGNATO CON METADATA

/**
 * Si rappresenta una variabile assegnata con metadata completi:
 * incapsula tutte le informazioni necessarie per il tracking di un assegnamento
 * durante l'algoritmo CDCL. Inoltre fornisce supporto per backtracking e
 * analisi dei conflitti attraverso i metadata dettagliati.
 *
 */
class AssignedLiteral {

    //region ATTRIBUTI CORE DELL'ASSEGNAMENTO

    /**
     * ID numerico della variabile assegnata.
     * Corrisponde agli ID generati da CNFFormula (sempre > 0).
     */
    private final Integer variable;

    /**
     * Valore booleano assegnato alla variabile.
     * true = variabile vera, false = variabile falsa
     */
    private final Boolean value;

    /**
     * Tipo di assegnamento distingue decisioni da implicazioni.
     * true = decisione euristica, false = implicazione unit propagation
     */
    private final Boolean isDecision;

    /**
     * Clausola che ha causato questa implicazione.
     * null per decisioni, richiesta per implicazioni.
     * Usata per conflict analysis e generazione prove.
     */
    private final List<Integer> ancestorClause;

    //endregion


    //region COSTRUZIONE CON VALIDAZIONE

    /**
     * Costruisce letterale assegnato con validazione completa dei parametri.
     *
     * VALIDAZIONI APPLICATE:
     * - Variable ID deve essere > 0 (range valido)
     * - Value non può essere null (assegnamento completo)
     * - IsDecision non può essere null (tipo definito)
     * - Implicazioni richiedono clausola ancestrale non vuota
     * - Decisioni non dovrebbero avere clausola ancestrale
     *
     * @param variable ID numerico variabile (> 0)
     * @param value valore booleano assegnato
     * @param isDecision true se decisione, false se implicazione
     * @param ancestorClause clausola causante (richiesta per implicazioni)
     * @throws IllegalArgumentException se parametri inconsistenti
     */
    public AssignedLiteral(Integer variable, Boolean value, Boolean isDecision, List<Integer> ancestorClause) {
        // Validazione parametri di base
        validateBasicParameters(variable, value, isDecision);

        // Validazione coerenza tipo-clausola
        validateTypeClauseConsistency(isDecision, ancestorClause);

        // Assegnazione con copia difensiva
        this.variable = variable;
        this.value = value;
        this.isDecision = isDecision;
        this.ancestorClause = ancestorClause != null ? new ArrayList<>(ancestorClause) : null;
    }

    /**
     * Valida parametri di base per consistenza.
     */
    private void validateBasicParameters(Integer variable, Boolean value, Boolean isDecision) {
        if (variable == null || variable <= 0) {
            throw new IllegalArgumentException("Variable ID deve essere > 0: " + variable);
        }
        if (value == null) {
            throw new IllegalArgumentException("Value non può essere null");
        }
        if (isDecision == null) {
            throw new IllegalArgumentException("IsDecision non può essere null");
        }
    }

    /**
     * Valida coerenza tra tipo assegnamento e clausola ancestrale.
     */
    private void validateTypeClauseConsistency(Boolean isDecision, List<Integer> ancestorClause) {
        if (!isDecision && (ancestorClause == null || ancestorClause.isEmpty())) {
            throw new IllegalArgumentException("Implicazioni richiedono clausola ancestrale");
        }
        if (isDecision && ancestorClause != null && !ancestorClause.isEmpty()) {
            throw new IllegalArgumentException("Decisioni non dovrebbero avere clausola ancestrale");
        }
    }

    //endregion


    //region INTERFACCIA PUBBLICA ACCESSORS

    /** @return ID numerico della variabile */
    public Integer getVariable() {
        return variable;
    }

    /** @return valore booleano assegnato */
    public Boolean getValue() {
        return value;
    }

    /** @return true se assegnamento è decisione euristica */
    public Boolean isDecision() {
        return isDecision;
    }

    /** @return true se assegnamento è implicazione unit propagation */
    public Boolean isImplication() {
        return !isDecision;
    }

    /** @return copia difensiva clausola ancestrale (null per decisioni) */
    public List<Integer> getAncestorClause() {
        return ancestorClause != null ? new ArrayList<>(ancestorClause) : null;
    }

    /** @return true se esiste clausola ancestrale */
    public boolean hasAncestorClause() {
        return ancestorClause != null && !ancestorClause.isEmpty();
    }

    //endregion


    //region UTILITÀ E CONVERSIONI

    /**
     * Converte in letterale DIMACS standard.
     * @return ID positivo se true, negativo se false
     */
    public Integer toDIMACSLiteral() {
        return value ? variable : -variable;
    }

    /**
     * Rappresentazione testuale per debugging con tutti i dettagli.
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("AssignedLiteral{");
        sb.append("var=").append(variable);
        sb.append(", val=").append(value);
        sb.append(", type=").append(isDecision ? "DECISION" : "IMPLICATION");

        if (hasAncestorClause()) {
            sb.append(", ancestor=").append(ancestorClause);
        }

        sb.append('}');
        return sb.toString();
    }

    /**
     * Uguaglianza basata su variabile e valore (ignora tipo e clausola).
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;

        AssignedLiteral that = (AssignedLiteral) obj;
        return Objects.equals(variable, that.variable) &&
                Objects.equals(value, that.value) &&
                Objects.equals(isDecision, that.isDecision);
    }

    @Override
    public int hashCode() {
        return Objects.hash(variable, value, isDecision);
    }

    //endregion
}



//region STACK GERARCHICO PER BACKTRACKING

/**
 * Si utilizza uno stack gerarchico per gestione livelli nell'algoritmo CDCL:
 * implementa la struttura dati per organizzazione gerarchica delle
 * decisioni e implicazioni durante la ricerca SAT. Inoltre fornisce supporto
 * per le operazioni di backtracking cronologico e non cronologico.
 *
 * ORGANIZZAZIONE GERARCHICA:
 * - Livello 0: implicazioni da clausole unitarie originali (sempre presente)
 * - Livello i (i>0): livello di decisione i con decisione + implicazioni
 * - Ogni livello mantiene cronologia completa degli assegnamenti
 * - Stack mai completamente vuoto
 */
class DecisionStack {

    private static final Logger LOGGER = Logger.getLogger(DecisionStack.class.getName());

    //region STRUTTURA DATI STACK GERARCHICO

    /**
     * Stack dei livelli di decisione con organizzazione gerarchica.
     *
     * STRUTTURA:
     * - Indice 0: livello 0 (implicazioni iniziali, sempre presente)
     * - Indice i>0: livello i di decisione
     * - Ogni livello è ArrayList<AssignedLiteral> con assegnamenti cronologici
     *
     * INVARIANTE: size() >= 1 (livello 0 sempre presente)
     */
    private final Stack<ArrayList<AssignedLiteral>> levelStack;

    //endregion


    //region INIZIALIZZAZIONE

    /**
     * Inizializza stack con livello 0 vuoto.
     * Il livello 0 è riservato a implicazioni da clausole unitarie originali.
     */
    public DecisionStack() {
        this.levelStack = new Stack<>();
        this.levelStack.push(new ArrayList<>()); // Livello 0 iniziale

        LOGGER.fine("DecisionStack inizializzato con livello 0");
    }

    //endregion


    //region OPERAZIONI DI AGGIUNTA

    /**
     * Aggiunge decisione euristica creando nuovo livello.
     *
     * ALGORITMO:
     * 1. Valida parametri di input per consistenza
     * 2. Crea assegnamento di decisione con metadata
     * 3. Inizializza nuovo livello con la decisione
     * 4. Aggiunge livello allo stack (incrementa altezza)
     * 5. Log informazioni per debugging
     *
     * @param variable ID variabile da decidere (> 0)
     * @param value valore booleano da assegnare
     * @throws IllegalArgumentException se parametri non validi
     */
    public void addDecision(Integer variable, Boolean value) {
        validateVariableAndValue(variable, value, "decisione");

        // Crea assegnamento decisionale
        AssignedLiteral decision = new AssignedLiteral(variable, value, true, null);

        // Inizializza nuovo livello
        ArrayList<AssignedLiteral> newLevel = new ArrayList<>();
        newLevel.add(decision);

        // Aggiunge al stack (operazione atomica)
        levelStack.push(newLevel);

        int currentLevel = levelStack.size() - 1;
        LOGGER.fine(String.format("Decisione aggiunta: var=%d, val=%s, livello=%d",
                variable, value, currentLevel));
    }

    /**
     * Aggiunge implicazione al livello corrente.
     *
     * ALGORITMO:
     * 1. Valida parametri e clausola ancestrale
     * 2. Verifica stato stack per consistenza
     * 3. Crea assegnamento di implicazione
     * 4. Modifica atomica del livello corrente
     * 5. Log con informazioni contestuali
     *
     * @param variable ID variabile implicata
     * @param value valore implicato
     * @param ancestorClause clausola causante l'implicazione
     * @throws IllegalArgumentException se parametri non validi
     * @throws IllegalStateException se stack inconsistente
     */
    public void addImpliedLiteral(Integer variable, Boolean value, List<Integer> ancestorClause) {
        validateVariableAndValue(variable, value, "implicazione");
        validateAncestorClause(ancestorClause);

        if (levelStack.isEmpty()) {
            throw new IllegalStateException("Stack vuoto - impossibile aggiungere implicazione");
        }

        // Crea implicazione con clausola ancestrale
        AssignedLiteral implication = new AssignedLiteral(variable, value, false, ancestorClause);

        // Modifica atomica del livello corrente
        ArrayList<AssignedLiteral> currentLevel = levelStack.pop();
        currentLevel.add(implication);
        levelStack.push(currentLevel);

        int levelIndex = levelStack.size() - 1;
        LOGGER.fine(String.format("Implicazione aggiunta: var=%d, val=%s, livello=%d, clausola=%s",
                variable, value, levelIndex, ancestorClause));
    }

    //endregion


    //region OPERAZIONI DI RIMOZIONE E BACKTRACKING

    /**
     * Rimuove livello più alto (backtracking cronologico).
     *
     * PROTEZIONI:
     * - Livello 0 è protetto e non può essere rimosso
     * - Operazione atomica per consistenza
     * - Restituisce copia difensiva degli assegnamenti rimossi
     *
     * @return assegnamenti del livello rimosso (vuoto se livello 0)
     */
    public ArrayList<AssignedLiteral> deleteLevel() {
        if (levelStack.size() <= 1) {
            LOGGER.warning("Tentativo rimozione livello 0 - operazione ignorata");
            return new ArrayList<>(); // Protezione livello 0
        }

        ArrayList<AssignedLiteral> removedLevel = levelStack.pop();
        int removedLevelIndex = levelStack.size(); // Indice del livello rimosso

        LOGGER.fine(String.format("Livello %d rimosso con %d assegnamenti",
                removedLevelIndex, removedLevel.size()));

        // Log dettagliato per debugging
        if (LOGGER.isLoggable(Level.FINEST)) {
            for (AssignedLiteral assignment : removedLevel) {
                LOGGER.finest("Rimosso: " + assignment);
            }
        }

        return new ArrayList<>(removedLevel); // Copia difensiva
    }

    /**
     * Backtracking non cronologico al livello target (backjumping).
     *
     * ALGORITMO:
     * 1. Valida livello target per safety
     * 2. Rimuove sequenzialmente livelli superiori
     * 3. Raccoglie tutti gli assegnamenti rimossi
     * 4. Log statistiche dell'operazione
     *
     * @param targetLevel livello di destinazione (>= 0)
     * @return tutti gli assegnamenti rimossi durante backjump
     * @throws IllegalArgumentException se targetLevel non valido
     */
    public List<AssignedLiteral> backtrackToLevel(int targetLevel) {
        int currentLevel = levelStack.size() - 1;
        validateBacktrackLevel(targetLevel, currentLevel);

        if (targetLevel == currentLevel) {
            LOGGER.fine("Backtrack al livello corrente - nessuna operazione");
            return new ArrayList<>();
        }

        List<AssignedLiteral> allRemovedAssignments = new ArrayList<>();

        // Rimozione sequenziale livelli
        while (levelStack.size() > targetLevel + 1) {
            ArrayList<AssignedLiteral> removedLevel = deleteLevel();
            allRemovedAssignments.addAll(removedLevel);
        }

        LOGGER.info(String.format("Backjump completato: %d → %d, rimossi %d assegnamenti",
                currentLevel, targetLevel, allRemovedAssignments.size()));

        return allRemovedAssignments;
    }

    //endregion


    //region OPERAZIONI DI INTERROGAZIONE

    /**
     * @return copia difensiva assegnamenti livello corrente
     */
    public ArrayList<AssignedLiteral> getTopLevel() {
        if (levelStack.isEmpty()) {
            throw new IllegalStateException("Stack vuoto - nessun livello disponibile");
        }
        return new ArrayList<>(levelStack.peek());
    }

    /**
     * @return livello corrente (numero di livelli - 1)
     */
    public int getLevel() {
        return levelStack.size() - 1;
    }

    /**
     * @return numero di livelli nello stack (sempre >= 1)
     */
    public int size() {
        return levelStack.size();
    }

    /**
     * @return ID variabili assegnate a livello specifico
     */
    public ArrayList<Integer> getLiteralsAtLevel(int levelIndex) {
        validateLevelIndex(levelIndex);

        List<AssignedLiteral> levelAssignments = levelStack.get(levelIndex);
        ArrayList<Integer> variableIds = new ArrayList<>();

        for (AssignedLiteral assignment : levelAssignments) {
            variableIds.add(assignment.getVariable());
        }

        return variableIds;
    }

    /**
     * @return tutti gli assegnamenti a livello specifico
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
     * Trova livello di una variabile specifica.
     * @return livello variabile o -1 se non trovata
     */
    public int findVariableLevel(Integer variable) {
        for (int level = 0; level < levelStack.size(); level++) {
            for (AssignedLiteral assignment : levelStack.get(level)) {
                if (assignment.getVariable().equals(variable)) {
                    return level;
                }
            }
        }
        return -1;
    }

    //endregion


    //region VALIDAZIONE PARAMETRI

    /**
     * Valida parametri variabile e valore.
     */
    private void validateVariableAndValue(Integer variable, Boolean value, String operationType) {
        if (variable == null || variable <= 0) {
            throw new IllegalArgumentException(
                    String.format("Variable ID non valido per %s: %s", operationType, variable));
        }
        if (value == null) {
            throw new IllegalArgumentException(
                    String.format("Value null non permesso per %s", operationType));
        }
    }

    /**
     * Valida clausola ancestrale per implicazioni.
     */
    private void validateAncestorClause(List<Integer> ancestorClause) {
        if (ancestorClause == null || ancestorClause.isEmpty()) {
            throw new IllegalArgumentException("AncestorClause richiesta per implicazioni");
        }

        for (Integer literal : ancestorClause) {
            if (literal == null || literal == 0) {
                throw new IllegalArgumentException("Letterale non valido: " + literal);
            }
        }
    }

    /**
     * Valida livello per operazioni backtrack.
     */
    private void validateBacktrackLevel(int targetLevel, int currentLevel) {
        if (targetLevel < 0) {
            throw new IllegalArgumentException("Target level negativo: " + targetLevel);
        }
        if (targetLevel > currentLevel) {
            throw new IllegalArgumentException(
                    String.format("Target level %d > current level %d", targetLevel, currentLevel));
        }
    }

    /**
     * Valida indice livello per accesso.
     */
    private void validateLevelIndex(int levelIndex) {
        if (levelIndex < 0 || levelIndex >= levelStack.size()) {
            throw new IndexOutOfBoundsException(
                    String.format("Level index %d fuori range [0, %d)", levelIndex, levelStack.size()));
        }
    }

    //endregion


    //region RAPPRESENTAZIONE TESTUALE

    /**
     * Rappresentazione completa per debugging.
     */
    @Override
    public String toString() {
        StringBuilder output = new StringBuilder();
        output.append("DecisionStack {\n");
        output.append(String.format("  Livelli: %d, Assegnamenti totali: %d\n",
                levelStack.size(), getTotalAssignments()));

        for (int levelIndex = 0; levelIndex < levelStack.size(); levelIndex++) {
            ArrayList<AssignedLiteral> level = levelStack.get(levelIndex);
            output.append(String.format("\n  Livello %d (%d assegnamenti):\n",
                    levelIndex, level.size()));

            if (level.isEmpty()) {
                output.append("    [vuoto]\n");
                continue;
            }

            for (AssignedLiteral assignment : level) {
                String type = assignment.isDecision() ? "DECISION" : "IMPLIED";
                String clauseInfo = assignment.hasAncestorClause()
                        ? " da " + assignment.getAncestorClause()
                        : "";

                output.append(String.format("    [%s] %d → %s%s\n",
                        type, assignment.getVariable(), assignment.getValue(), clauseInfo));
            }
        }

        output.append("}");
        return output.toString();
    }

    //endregion
}