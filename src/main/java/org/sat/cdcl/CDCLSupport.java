package org.sat.cdcl;

import org.sat.cnf.CNFConverter;
import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;

/**
 * Classi di supporto per il solutore SAT CDCL.
 *
 * Questo modulo fornisce le strutture dati fondamentali per l'implementazione
 * dell'algoritmo CDCL (Conflict-Driven Clause Learning), ottimizzate per
 * prestazioni ed efficienza di memoria.
 *
 * Componenti Principali:
 * - CNFFormula: Rappresentazione interna ottimizzata delle formule CNF
 * - AssignedLiteral: Modello per letterali assegnati con metadata di tracciamento
 * - DecisionStack: Stack gerarchico per gestione livelli di decisione e backtracking
 * - Classi di risultato: Encapsulation dei risultati delle operazioni CDCL
 *
 * Ottimizzazioni Implementate:
 * - Mapping efficiente variabili simboliche → identificatori numerici
 * - Strutture dati a accesso O(1) per operazioni critiche
 * - Gestione memoria con prevenzione di memory leak
 * - Logging dettagliato per debugging e analisi prestazioni
 *
 */

// ========================================
// RAPPRESENTAZIONE FORMULA CNF
// ========================================

/**
 * Rappresentazione interna ottimizzata di una formula in forma normale congiuntiva (CNF).
 *
 * Questa classe converte la rappresentazione ad albero di CNFConverter in una struttura
 * dati ottimizzata per l'algoritmo CDCL, utilizzando identificatori numerici per
 * le variabili e liste di interi per le clausole.
 *
 * Vantaggi della Rappresentazione:
 * - Accesso O(1) alle clausole
 * - Rappresentazione compatta in memoria
 * - Operazioni arithmetiche veloci sui letterali
 * - Mapping bidirezionale variabili simboliche ↔ numeriche
 *
 * Formato Interno:
 * - Clausole: List<List<Integer>> dove ogni Integer rappresenta un letterale
 * - Letterali positivi: numeri positivi (es. 5 = variabile 5 vera)
 * - Letterali negativi: numeri negativi (es. -5 = variabile 5 falsa)
 * - Mapping: "P" → 1, "Q" → 2, etc.
 */
class CNFFormula {

    // ========================================
    // LOGGING E COSTANTI
    // ========================================

    /** Logger dedicato per tracciamento operazioni della formula CNF */
    private static final Logger LOGGER = Logger.getLogger(CNFFormula.class.getName());

    /** Messaggio di warning per letterali non riconosciuti durante la conversione */
    private static final String UNRECOGNIZED_LITERAL_WARNING = "Letterale non riconosciuto durante conversione: ";

    // ========================================
    // STRUTTURE DATI PRINCIPALI
    // ========================================

    /**
     * Lista delle clausole della formula CNF.
     * Ogni clausola è rappresentata come List<Integer> di letterali.
     * Esempio: [[1, -2], [2, 3]] rappresenta (P ∨ ¬Q) ∧ (Q ∨ R)
     */
    private final List<List<Integer>> clauses;

    /**
     * Numero totale di variabili distinte nella formula.
     * Corrisponde alla dimensione del dominio delle variabili [1..variableCount].
     */
    private final int variableCount;

    /**
     * Mapping bidirezionale da nomi simbolici a identificatori numerici.
     * Chiave: nome simbolico (es. "P", "Q", "var1")
     * Valore: identificatore numerico univoco (es. 1, 2, 3)
     *
     * Invariante: ogni nome simbolico ha un ID univoco ≥ 1
     */
    private final Map<String, Integer> variableMapping;

    // ========================================
    // COSTRUZIONE E INIZIALIZZAZIONE
    // ========================================

    /**
     * Costruisce una rappresentazione CNF ottimizzata dalla rappresentazione ad albero.
     *
     * Il processo di conversione comprende:
     * 1. Attraversamento ricorsivo dell'albero CNFConverter
     * 2. Estrazione e catalogazione di tutte le variabili simboliche
     * 3. Assegnazione di identificatori numerici univoci
     * 4. Conversione delle clausole in formato List<Integer>
     * 5. Validazione dell'integrità della rappresentazione risultante
     *
     * @param cnfConverter formula CNF in formato albero da convertire
     * @throws IllegalArgumentException se la formula è malformata o nulla
     */
    public CNFFormula(CNFConverter cnfConverter) {
        // Validazione input
        if (cnfConverter == null) {
            throw new IllegalArgumentException("CNFConverter non può essere null");
        }

        LOGGER.info("=== INIZIO CONVERSIONE FORMULA CNF ===");

        // Inizializzazione strutture dati
        this.clauses = new ArrayList<>();
        this.variableMapping = new LinkedHashMap<>(); // Mantiene ordine di inserimento per determinismo

        try {
            // Conversione principale dalla rappresentazione ad albero
            performConversionFromCNFConverter(cnfConverter);

            // Calcolo delle variabili totali (non le singole occorrenze)
            this.variableCount = variableMapping.size();

            // Validazione risultato
            validateConversionResult();

            // Logging informazioni formula
            logFormulaStatistics();

        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Errore durante conversione CNF", e);
            throw new RuntimeException("Fallita conversione formula CNF: " + e.getMessage(), e);
        }

        LOGGER.info("=== CONVERSIONE CNF COMPLETATA CON SUCCESSO ===");
    }

    // ========================================
    // CONVERSIONE DALLA RAPPRESENTAZIONE AD ALBERO
    // ========================================

    /**
     * Esegue la conversione principale dalla rappresentazione CNFConverter.
     *
     * Gestisce due casi principali:
     * - Formula AND: congiunzione di multiple clausole
     * - Formula semplice: singola clausola o letterale
     *
     * @param converter nodo radice della rappresentazione ad albero
     */
    private void performConversionFromCNFConverter(CNFConverter converter) {
        LOGGER.fine("Inizio conversione da CNFConverter tipo: " + converter.type);

        if (converter.type == CNFConverter.Type.AND) {
            // Caso 1: Formula complessa - congiunzione di clausole
            processConjunctionOfClauses(converter);
        } else {
            // Caso 2: Formula semplice - singola clausola o letterale
            processSingleClause(converter);
        }

        LOGGER.fine("Conversione completata - clausole estratte: " + clauses.size());
    }

    /**
     * Processa una congiunzione di clausole (formula complessa).
     *
     * @param conjunctionNode nodo AND contenente le clausole operando
     */
    private void processConjunctionOfClauses(CNFConverter conjunctionNode) {
        if (conjunctionNode.operands == null || conjunctionNode.operands.isEmpty()) {
            LOGGER.warning("Nodo AND senza operandi - formula vuota");
            return;
        }

        LOGGER.fine("Processando congiunzione con " + conjunctionNode.operands.size() + " clausole");

        // Processa ogni clausola della congiunzione
        for (CNFConverter clauseNode : conjunctionNode.operands) {
            List<Integer> convertedClause = convertSingleClause(clauseNode);

            if (isValidClause(convertedClause)) {
                clauses.add(convertedClause);
                LOGGER.finest("Aggiunta clausola: " + convertedClause);
            } else {
                LOGGER.warning("Clausola scartata (vuota o non valida): " + clauseNode);
            }
        }
    }

    /**
     * Processa una formula semplice (singola clausola).
     *
     * @param singleNode nodo rappresentante la clausola singola
     */
    private void processSingleClause(CNFConverter singleNode) {
        LOGGER.fine("Processando clausola singola di tipo: " + singleNode.type);

        List<Integer> convertedClause = convertSingleClause(singleNode);

        if (isValidClause(convertedClause)) {
            clauses.add(convertedClause);
            LOGGER.fine("Aggiunta clausola singola: " + convertedClause);
        } else {
            LOGGER.warning("Clausola singola scartata (non valida)");
        }
    }

    /**
     * Converte una singola clausola dalla rappresentazione ad albero.
     *
     * Gestisce i tipi di clausola:
     * - OR: disgiunzione di letterali (clausola normale)
     * - ATOM/NOT: letterale singolo (clausola unitaria)
     *
     * @param clauseNode nodo rappresentante la clausola
     * @return lista di letterali convertiti
     */
    private List<Integer> convertSingleClause(CNFConverter clauseNode) {
        List<Integer> literals = new ArrayList<>();

        switch (clauseNode.type) {
            case OR:
                // Clausola con multipli letterali
                literals = convertDisjunctionClause(clauseNode);
                break;

            case ATOM:
            case NOT:
                // Clausola unitaria (singolo letterale)
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
     * Converte una clausola di tipo OR (disgiunzione di letterali).
     *
     * @param orNode nodo OR contenente i letterali operando
     * @return lista dei letterali convertiti
     */
    private List<Integer> convertDisjunctionClause(CNFConverter orNode) {
        List<Integer> literals = new ArrayList<>();

        if (orNode.operands == null) {
            LOGGER.warning("Nodo OR senza operandi");
            return literals;
        }

        LOGGER.finest("Convertendo disgiunzione con " + orNode.operands.size() + " letterali");

        // Converte ogni letterale della disgiunzione
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
     * Gestisce i casi:
     * - ATOM: letterale positivo (es. P → 1)
     * - NOT ATOM: letterale negativo (es. ¬P → -1)
     *
     * @param literalNode nodo rappresentante il letterale
     * @return identificatore numerico del letterale (positivo/negativo) o null se non convertibile
     */
    private Integer convertSingleLiteral(CNFConverter literalNode) {
        switch (literalNode.type) {
            case ATOM:
                // Letterale positivo: P → ID_P
                return convertPositiveLiteral(literalNode);

            case NOT:
                // Letterale negativo: ¬P → -ID_P
                return convertNegativeLiteral(literalNode);

            default:
                LOGGER.warning(UNRECOGNIZED_LITERAL_WARNING + literalNode.type);
                return null;
        }
    }

    /**
     * Converte un letterale positivo (variabile atomica).
     *
     * @param atomNode nodo ATOM contenente il nome della variabile
     * @return identificatore numerico positivo della variabile
     */
    private Integer convertPositiveLiteral(CNFConverter atomNode) {
        if (atomNode.atom == null || atomNode.atom.trim().isEmpty()) {
            LOGGER.warning("Nome variabile vuoto o null in nodo ATOM");
            return null;
        }

        String variableName = atomNode.atom.trim();
        Integer variableId = getOrCreateVariableId(variableName);

        LOGGER.finest("Letterale positivo: " + variableName + " → " + variableId);
        return variableId;
    }

    /**
     * Converte un letterale negativo (negazione di variabile atomica).
     *
     * @param notNode nodo NOT contenente la variabile da negare
     * @return identificatore numerico negativo della variabile
     */
    private Integer convertNegativeLiteral(CNFConverter notNode) {
        // Verifica struttura NOT(ATOM)
        if (notNode.operand == null) {
            LOGGER.warning("Nodo NOT senza operando");
            return null;
        }

        if (notNode.operand.type != CNFConverter.Type.ATOM) {
            LOGGER.warning("NOT applicato a non-ATOM: " + notNode.operand.type);
            return null;
        }

        if (notNode.operand.atom == null || notNode.operand.atom.trim().isEmpty()) {
            LOGGER.warning("Nome variabile vuoto in NOT(ATOM)");
            return null;
        }

        String variableName = notNode.operand.atom.trim();
        Integer variableId = getOrCreateVariableId(variableName);
        Integer negatedId = -variableId;

        LOGGER.finest("Letterale negativo: ¬" + variableName + " → " + negatedId);
        return negatedId;
    }

    // ========================================
    // GESTIONE MAPPING VARIABILI
    // ========================================

    /**
     * Ottiene l'identificatore numerico di una variabile, creandolo se necessario.
     *
     * Questo metodo implementa il mapping lazy: gli identificatori vengono assegnati
     * progressivamente nell'ordine di primo incontro delle variabili.
     *
     * @param variableName nome simbolico della variabile
     * @return identificatore numerico univoco (sempre > 0)
     */
    private Integer getOrCreateVariableId(String variableName) {
        // Usa computeIfAbsent per atomicità e efficienza
        Integer variableId = variableMapping.computeIfAbsent(variableName, name -> {
            int newId = variableMapping.size() + 1;
            LOGGER.finest("Nuova variabile mappata: " + name + " → " + newId);
            return newId;
        });

        return variableId;
    }

    // ========================================
    // VALIDAZIONE E DIAGNOSTICA
    // ========================================

    /**
     * Verifica se una clausola convertita è valida.
     *
     * @param clause clausola da validare
     * @return true se la clausola è valida (non null e non vuota)
     */
    private boolean isValidClause(List<Integer> clause) {
        return clause != null && !clause.isEmpty();
    }

    /**
     * Valida il risultato della conversione per detectare inconsistenze.
     *
     * @throws IllegalStateException se la conversione ha prodotto risultati inconsistenti
     */
    private void validateConversionResult() {
        // Verifica coerenza conteggio variabili
        if (variableCount != variableMapping.size()) {
            throw new IllegalStateException("Inconsistenza nel conteggio variabili: " +
                    variableCount + " != " + variableMapping.size());
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

        // Verifica del range degli ID delle variabili nelle clausole
        for (List<Integer> clause : clauses) {
            for (Integer literal : clause) {
                int absLiteral = Math.abs(literal);
                if (absLiteral <= 0 || absLiteral > variableCount) {
                    throw new IllegalStateException("Letterale fuori range: " + literal +
                            " (range valido: 1-" + variableCount + ")");
                }
            }
        }

        LOGGER.fine("Validazione conversione CNF: SUCCESSO");
    }

    /**
     * Registra statistiche dettagliate sulla formula convertita.
     */
    private void logFormulaStatistics() {
        // Si calcolano tutte le occorrenze dei letterali
        int totalLiterals = clauses.stream().mapToInt(List::size).sum();

        // Si calcola la lunghezza media delle clausole
        double avgClauseLength = clauses.isEmpty() ? 0.0 : (double) totalLiterals / clauses.size();

        LOGGER.info(String.format("Formula CNF creata: %d clausole, %d variabili, %.1f letterali/clausola media",
                clauses.size(), variableCount, avgClauseLength));

        // Log mapping variabili per debugging
        if (LOGGER.isLoggable(Level.FINE)) {
            LOGGER.fine("Mapping variabili: " + variableMapping);
        }

        // Log distribuzione lunghezza clausole per analisi
        if (LOGGER.isLoggable(Level.FINEST)) {
            Map<Integer, Long> lengthDistribution = clauses.stream()
                    .collect(java.util.stream.Collectors.groupingBy(
                            List::size, java.util.stream.Collectors.counting()));
            LOGGER.finest("Distribuzione lunghezza clausole: " + lengthDistribution);
        }
    }

    // ========================================
    // INTERFACCIA PUBBLICA
    // ========================================

    /**
     * Restituisce la lista immutabile delle clausole.
     *
     * @return copia difensiva delle clausole per prevenire modifiche esterne
     */
    public List<List<Integer>> getClauses() {
        return new ArrayList<>(clauses);
    }

    /**
     * Restituisce il numero totale di variabili distinte.
     *
     * @return conteggio variabili (sempre ≥ 0)
     */
    public int getVariableCount() {
        return variableCount;
    }

    /**
     * Restituisce il numero totale di clausole.
     *
     * @return conteggio clausole (sempre ≥ 0)
     */
    public int getClausesCount() {
        return clauses.size();
    }

    /**
     * Restituisce il mapping da nomi simbolici a identificatori numerici.
     *
     * @return copia difensiva del mapping per prevenire modifiche esterne
     */
    public Map<String, Integer> getVariableMapping() {
        return new LinkedHashMap<>(variableMapping);
    }

    /**
     * Rappresentazione testuale della formula per debugging.
     *
     * @return stringa descrittiva con statistiche e contenuto della formula
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("CNFFormula{");
        sb.append("clausole=").append(clauses.size());
        sb.append(", variabili=").append(variableCount);
        sb.append(", mapping=").append(variableMapping);
        sb.append(", clausole=").append(clauses);
        sb.append('}');
        return sb.toString();
    }
}

// ========================================
// MODELLO LETTERALE ASSEGNATO
// ========================================

/**
 * Rappresenta un letterale (variabile) assegnato durante il processo CDCL.
 *
 * Questa classe incapsula tutte le informazioni necessarie per il tracking
 * di un assegnamento di variabile, inclusi metadata per backtracking e
 * analisi dei conflitti.
 *
 * Informazioni Tracciate:
 * - Identità della variabile e valore assegnato
 * - Tipo di assegnamento (decisione vs. implicazione)
 * - Clausola ancestrale (per implicazioni)
 * - Metadata per debugging e analisi
 *
 * Thread Safety: Immutabile dopo costruzione
 */
class AssignedLiteral {

    // ========================================
    // ATTRIBUTI PRINCIPALI
    // ========================================

    /**
     * Identificatore numerico della variabile assegnata.
     * Corrisponde agli ID generati dalla CNFFormula (sempre > 0).
     */
    private final Integer variable;

    /**
     * Valore booleano assegnato alla variabile.
     * true = variabile vera, false = variabile falsa
     */
    private final Boolean value;

    /**
     * Flag che indica il tipo di assegnamento.
     * true = decisione (scelta del solver), false = implicazione (dedotta da propagazione)
     */
    private final Boolean isDecision;

    /**
     * Clausola che ha causato questa implicazione (null per decisioni).
     * Utilizzata per analisi conflitti e generazione prove.
     * Formato: List<Integer> di letterali (esempio: [1, -2, 3])
     */
    private final List<Integer> ancestorClause;

    // ========================================
    // COSTRUZIONE
    // ========================================

    /**
     * Costruisce un nuovo letterale assegnato con metadata completi.
     *
     * @param variable identificatore numerico della variabile (deve essere > 0)
     * @param value valore booleano assegnato
     * @param isDecision true se è una decisione, false se è un'implicazione
     * @param ancestorClause clausola causante (richiesta per implicazioni, null per decisioni)
     * @throws IllegalArgumentException se i parametri sono inconsistenti
     */
    public AssignedLiteral(Integer variable, Boolean value, Boolean isDecision, List<Integer> ancestorClause) {
        // Validazione parametri
        validateConstructorParameters(variable, value, isDecision, ancestorClause);

        // Assegnazione con copia difensiva per immutabilità
        this.variable = variable;
        this.value = value;
        this.isDecision = isDecision;
        this.ancestorClause = ancestorClause != null ? new ArrayList<>(ancestorClause) : null;
    }

    /**
     * Valida i parametri del costruttore per garantire coerenza.
     *
     * @param variable identificatore variabile
     * @param value valore assegnato
     * @param isDecision tipo assegnamento
     * @param ancestorClause clausola ancestrale
     * @throws IllegalArgumentException se i parametri sono inconsistenti
     */
    private void validateConstructorParameters(Integer variable, Boolean value, Boolean isDecision, List<Integer> ancestorClause) {
        if (variable == null || variable <= 0) {
            throw new IllegalArgumentException("Variable ID deve essere > 0, ricevuto: " + variable);
        }

        if (value == null) {
            throw new IllegalArgumentException("Value non può essere null");
        }

        if (isDecision == null) {
            throw new IllegalArgumentException("IsDecision non può essere null");
        }

        // Verifica coerenza: implicazioni devono avere clausola ancestrale
        if (!isDecision && (ancestorClause == null || ancestorClause.isEmpty())) {
            throw new IllegalArgumentException("Implicazioni richiedono clausola ancestrale non vuota");
        }

        // Verifica coerenza: decisioni non dovrebbero avere clausola ancestrale
        if (isDecision && ancestorClause != null && !ancestorClause.isEmpty()) {
            throw new IllegalArgumentException("Decisioni non dovrebbero avere clausola ancestrale");
        }
    }

    // ========================================
    // INTERFACCIA PUBBLICA
    // ========================================

    /**
     * Restituisce l'identificatore numerico della variabile.
     *
     * @return ID variabile (sempre > 0)
     */
    public Integer getVariable() {
        return variable;
    }

    /**
     * Restituisce il valore booleano assegnato.
     *
     * @return true se variabile vera, false se falsa
     */
    public Boolean getValue() {
        return value;
    }

    /**
     * Verifica se questo assegnamento è una decisione.
     *
     * @return true se decisione del solver, false se implicazione
     */
    public Boolean isDecision() {
        return isDecision;
    }

    /**
     * Verifica se questo assegnamento è un'implicazione.
     *
     * @return true se implicazione, false se decisione
     */
    public Boolean isImplication() {
        return !isDecision;
    }

    /**
     * Restituisce la clausola che ha causato questa implicazione.
     *
     * @return copia difensiva della clausola ancestrale, null per decisioni
     */
    public List<Integer> getAncestorClause() {
        return ancestorClause != null ? new ArrayList<>(ancestorClause) : null;
    }

    /**
     * Verifica se questo assegnamento ha una clausola ancestrale.
     *
     * @return true se esiste clausola ancestrale
     */
    public boolean hasAncestorClause() {
        return ancestorClause != null && !ancestorClause.isEmpty();
    }

    /**
     * Genera rappresentazione del letterale nel formato standard DIMACS.
     *
     * @return letterale in formato DIMACS (positivo/negativo)
     */
    public Integer toDIMACSLiteral() {
        return value ? variable : -variable;
    }

    // ========================================
    // UTILITÀ E DEBUGGING
    // ========================================

    /**
     * Rappresentazione testuale dettagliata per debugging.
     *
     * @return stringa descrittiva con tutti i dettagli del letterale
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
     * Confronto per uguaglianza basato su variabile e valore.
     *
     * @param obj oggetto da confrontare
     * @return true se rappresentano lo stesso assegnamento
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

    /**
     * Hash code basato su variabile, valore e tipo.
     *
     * @return hash code per uso in collezioni
     */
    @Override
    public int hashCode() {
        return Objects.hash(variable, value, isDecision);
    }
}

// ========================================
// STACK DECISIONI GERARCHICO
// ========================================

/**
 * Stack gerarchico per gestione dei livelli di decisione nell'algoritmo CDCL.
 *
 * Questa struttura dati specializzata gestisce l'organizzazione gerarchica
 * delle decisioni e implicazioni durante la ricerca SAT, fornendo supporto
 * efficiente per operazioni di backtracking non cronologico.
 *
 * Organizzazione:
 * - Livello 0: implicazioni da clausole unitarie originali
 * - Livello 1+: livelli di decisione con decisioni e implicazioni conseguenti
 * - Ogni livello mantiene cronologia completa degli assegnamenti
 *
 * Operazioni Supportate:
 * - Aggiunta decisioni (creazione nuovo livello)
 * - Aggiunta implicazioni (al livello corrente)
 * - Backtracking a livello specifico
 * - Interrogazione stato corrente
 *
 * Invarianti:
 * - Livello 0 sempre presente (può essere vuoto)
 * - Ogni livello ≥ 1 inizia con esattamente una decisione
 * - Implicazioni sempre aggiunte al livello corrente
 * - Stack mai completamente vuoto
 */
class DecisionStack {

    // ========================================
    // LOGGING E COSTANTI
    // ========================================

    /** Logger dedicato per operazioni dello stack decisioni */
    private static final Logger LOGGER = Logger.getLogger(DecisionStack.class.getName());

    /** Messaggio di warning per tentativi di rimozione del livello 0 */
    private static final String LEVEL_ZERO_REMOVAL_WARNING =
            "Tentativo di rimuovere livello 0 - operazione non permessa";

    // ========================================
    // STRUTTURA DATI PRINCIPALE
    // ========================================

    /**
     * Stack dei livelli di decisione.
     *
     * Organizzazione:
     * - Indice 0: livello 0 (implicazioni iniziali)
     * - Indice i (i>0): livello i di decisione
     * - Ogni elemento è ArrayList<AssignedLiteral> contenente gli assegnamenti del livello
     *
     * Invariante: sempre contiene almeno il livello 0
     */
    private final Stack<ArrayList<AssignedLiteral>> procedureStack;

    // ========================================
    // COSTRUZIONE E INIZIALIZZAZIONE
    // ========================================

    /**
     * Inizializza lo stack con il livello 0 vuoto.
     *
     * Il livello 0 è riservato alle implicazioni derivanti da clausole unitarie
     * della formula originale, prima di qualsiasi decisione del solver.
     */
    public DecisionStack() {
        this.procedureStack = new Stack<>();

        // Inizializza livello 0 vuoto
        this.procedureStack.push(new ArrayList<>());

        LOGGER.fine("DecisionStack inizializzato con livello 0");
    }

    // ========================================
    // OPERAZIONI DI AGGIUNTA
    // ========================================

    /**
     * Aggiunge una nuova decisione creando un nuovo livello.
     *
     * Le decisioni rappresentano scelte euristiche del solver e sempre
     * iniziano un nuovo livello di decisione. Il livello creato conterrà
     * la decisione iniziale e tutte le implicazioni conseguenti.
     *
     * @param variable identificatore numerico della variabile da decidere
     * @param value valore booleano da assegnare alla variabile
     * @throws IllegalArgumentException se variable ≤ 0 o value è null
     */
    public void addDecision(Integer variable, Boolean value) {
        // Validazione parametri
        validateVariableAndValue(variable, value, "decisione");

        // Crea l'assegnamento decisionale
        AssignedLiteral decision = new AssignedLiteral(variable, value, true, null);

        // Crea nuovo livello con la decisione
        ArrayList<AssignedLiteral> newLevel = new ArrayList<>();
        newLevel.add(decision);

        // Aggiungi il nuovo livello allo stack
        procedureStack.push(newLevel);

        // Logging con informazioni dettagliate
        int currentLevel = procedureStack.size() - 1;
        LOGGER.fine(String.format("Decisione aggiunta: var=%d, val=%s, livello=%d",
                variable, value, currentLevel));

        logStackState("dopo aggiunta decisione");
    }

    /**
     * Aggiunge un'implicazione al livello di decisione corrente.
     *
     * Le implicazioni sono assegnamenti dedotti dalla propagazione unitaria
     * e vengono sempre aggiunte al livello di decisione attualmente attivo.
     *
     * @param variable identificatore numerico della variabile implicata
     * @param value valore booleano implicato per la variabile
     * @param ancestorClause clausola che ha causato l'implicazione
     * @throws IllegalArgumentException se parametri non validi
     * @throws IllegalStateException se lo stack è in stato inconsistente
     */
    public void addImpliedLiteral(Integer variable, Boolean value, List<Integer> ancestorClause) {
        // Validazione parametri
        validateVariableAndValue(variable, value, "implicazione");
        validateAncestorClause(ancestorClause);

        // Validazione stato stack
        if (procedureStack.isEmpty()) {
            throw new IllegalStateException("Stack vuoto - impossibile aggiungere implicazione");
        }

        // Crea l'assegnamento di implicazione
        AssignedLiteral implication = new AssignedLiteral(variable, value, false, ancestorClause);

        // Modifica atomica del livello corrente
        ArrayList<AssignedLiteral> currentLevel = procedureStack.pop();
        currentLevel.add(implication);
        procedureStack.push(currentLevel);

        // Logging con contesto
        int levelIndex = procedureStack.size() - 1;
        LOGGER.fine(String.format("Implicazione aggiunta: var=%d, val=%s, livello=%d, clausola=%s",
                variable, value, levelIndex, ancestorClause));

        logStackState("dopo aggiunta implicazione");
    }

    // ========================================
    // OPERAZIONI DI RIMOZIONE E BACKTRACKING
    // ========================================

    /**
     * Rimuove e restituisce il livello di decisione più alto.
     *
     * Questa operazione implementa il backtracking cronologico rimuovendo
     * l'ultimo livello aggiunto. Il livello 0 è protetto e non può essere rimosso.
     *
     * @return lista degli assegnamenti del livello rimosso
     * @throws IllegalStateException se si tenta di rimuovere il livello 0
     */
    public ArrayList<AssignedLiteral> deleteLevel() {
        // Protezione livello 0
        if (procedureStack.size() <= 1) {
            LOGGER.warning(LEVEL_ZERO_REMOVAL_WARNING);
            return new ArrayList<>(); // Restituisce lista vuota invece di modificare lo stato
        }

        // Rimozione sicura del livello
        ArrayList<AssignedLiteral> removedLevel = procedureStack.pop();
        int removedLevelIndex = procedureStack.size(); // Indice del livello appena rimosso

        LOGGER.fine(String.format("Livello %d rimosso con %d letterali",
                removedLevelIndex, removedLevel.size()));

        // Log dettagliato degli assegnamenti rimossi
        if (LOGGER.isLoggable(Level.FINEST)) {
            logRemovedAssignments(removedLevel, removedLevelIndex);
        }

        logStackState("dopo rimozione livello");

        // Restituisce copia difensiva
        return new ArrayList<>(removedLevel);
    }

    /**
     * Esegue backtracking non cronologico al livello specificato.
     *
     * Rimuove tutti i livelli superiori al target, implementando
     * il backjumping caratteristico dell'algoritmo CDCL.
     *
     * @param targetLevel livello di destinazione del backtrack
     * @return lista di tutti gli assegnamenti rimossi
     * @throws IllegalArgumentException se targetLevel < 0 o > livello corrente
     */
    public List<AssignedLiteral> backtrackToLevel(int targetLevel) {
        // Validazione livello target
        int currentLevel = procedureStack.size() - 1;
        validateBacktrackLevel(targetLevel, currentLevel);

        if (targetLevel == currentLevel) {
            LOGGER.fine("Backtrack richiesto al livello corrente - nessuna operazione");
            return new ArrayList<>();
        }

        // Raccolta assegnamenti rimossi per analisi
        List<AssignedLiteral> allRemovedAssignments = new ArrayList<>();

        // Rimozione sequenziale dei livelli
        while (procedureStack.size() > targetLevel + 1) {
            ArrayList<AssignedLiteral> removedLevel = deleteLevel();
            allRemovedAssignments.addAll(removedLevel);
        }

        LOGGER.info(String.format("Backtrack completato: livello %d → %d, rimossi %d assegnamenti",
                currentLevel, targetLevel, allRemovedAssignments.size()));

        return allRemovedAssignments;
    }

    // ========================================
    // OPERAZIONI DI INTERROGAZIONE
    // ========================================

    /**
     * Restituisce il livello di decisione più alto senza rimuoverlo.
     *
     * @return copia difensiva degli assegnamenti del livello corrente
     */
    public ArrayList<AssignedLiteral> getTopLevel() {
        if (procedureStack.isEmpty()) {
            throw new IllegalStateException("Stack vuoto - nessun livello disponibile");
        }

        return new ArrayList<>(procedureStack.peek());
    }

    /**
     * Restituisce il numero di livelli nello stack.
     *
     * @return dimensione stack (sempre ≥ 1 per presenza garantita del livello 0)
     */
    public int size() {
        return procedureStack.size();
    }

    /**
     * Restituisce gli identificatori delle variabili assegnate a un livello specifico.
     *
     * @param levelIndex indice del livello (0-based)
     * @return lista degli ID delle variabili assegnate al livello
     * @throws IndexOutOfBoundsException se levelIndex non valido
     */
    public ArrayList<Integer> getLiteralsAtLevel(int levelIndex) {
        validateLevelIndex(levelIndex);

        List<AssignedLiteral> levelAssignments = procedureStack.get(levelIndex);
        ArrayList<Integer> variableIds = new ArrayList<>();

        for (AssignedLiteral assignment : levelAssignments) {
            variableIds.add(assignment.getVariable());
        }

        return variableIds;
    }

    /**
     * Restituisce tutti gli assegnamenti a un livello specifico.
     *
     * @param levelIndex indice del livello
     * @return copia difensiva degli assegnamenti del livello
     * @throws IndexOutOfBoundsException se levelIndex non valido
     */
    public List<AssignedLiteral> getAssignmentsAtLevel(int levelIndex) {
        validateLevelIndex(levelIndex);
        return new ArrayList<>(procedureStack.get(levelIndex));
    }

    /**
     * Verifica se lo stack contiene solo il livello 0 vuoto.
     *
     * @return true se stack effettivamente vuoto (nessun assegnamento)
     */
    public boolean isEmpty() {
        return procedureStack.size() == 1 && procedureStack.peek().isEmpty();
    }

    /**
     * Calcola il numero totale di assegnamenti in tutti i livelli.
     *
     * @return conteggio totale assegnamenti
     */
    public int getTotalAssignments() {
        return procedureStack.stream()
                .mapToInt(ArrayList::size)
                .sum();
    }

    /**
     * Trova il livello di decisione di una variabile specifica.
     *
     * @param variable identificatore della variabile
     * @return livello della variabile o -1 se non trovata
     */
    public int findVariableLevel(Integer variable) {
        for (int level = 0; level < procedureStack.size(); level++) {
            for (AssignedLiteral assignment : procedureStack.get(level)) {
                if (assignment.getVariable().equals(variable)) {
                    return level;
                }
            }
        }
        return -1; // Variabile non trovata
    }

    // ========================================
    // VALIDAZIONE E CONTROLLI
    // ========================================

    /**
     * Valida parametri variabile e valore.
     */
    private void validateVariableAndValue(Integer variable, Boolean value, String operationType) {
        if (variable == null || variable <= 0) {
            throw new IllegalArgumentException(String.format(
                    "Variable ID non valido per %s: %s (deve essere > 0)", operationType, variable));
        }

        if (value == null) {
            throw new IllegalArgumentException(String.format(
                    "Value non può essere null per %s", operationType));
        }
    }

    /**
     * Valida clausola ancestrale per implicazioni.
     */
    private void validateAncestorClause(List<Integer> ancestorClause) {
        if (ancestorClause == null || ancestorClause.isEmpty()) {
            throw new IllegalArgumentException("AncestorClause richiesta per implicazioni");
        }

        // Verifica che tutti i letterali siano validi
        for (Integer literal : ancestorClause) {
            if (literal == null || literal == 0) {
                throw new IllegalArgumentException("Letterale non valido in ancestorClause: " + literal);
            }
        }
    }

    /**
     * Valida livello per operazioni di backtrack.
     */
    private void validateBacktrackLevel(int targetLevel, int currentLevel) {
        if (targetLevel < 0) {
            throw new IllegalArgumentException("Target level non può essere negativo: " + targetLevel);
        }

        if (targetLevel > currentLevel) {
            throw new IllegalArgumentException(String.format(
                    "Target level %d > current level %d", targetLevel, currentLevel));
        }
    }

    /**
     * Valida indice di livello per accesso.
     */
    private void validateLevelIndex(int levelIndex) {
        if (levelIndex < 0 || levelIndex >= procedureStack.size()) {
            throw new IndexOutOfBoundsException(String.format(
                    "Level index %d fuori range [0, %d)", levelIndex, procedureStack.size()));
        }
    }

    // ========================================
    // LOGGING E DEBUGGING
    // ========================================

    /**
     * Registra lo stato corrente dello stack per debugging.
     */
    private void logStackState(String context) {
        if (!LOGGER.isLoggable(Level.FINEST)) return;

        LOGGER.finest(String.format("Stack state %s: %d livelli, %d assegnamenti totali",
                context, procedureStack.size(), getTotalAssignments()));
    }

    /**
     * Registra dettagli degli assegnamenti rimossi.
     */
    private void logRemovedAssignments(ArrayList<AssignedLiteral> removedLevel, int levelIndex) {
        for (AssignedLiteral assignment : removedLevel) {
            LOGGER.finest(String.format("Rimosso da livello %d: %s", levelIndex, assignment));
        }
    }

    // ========================================
    // RAPPRESENTAZIONE TESTUALE
    // ========================================

    /**
     * Genera rappresentazione testuale completa dello stack per debugging.
     *
     * @return stringa multi-linea con struttura completa dello stack
     */
    @Override
    public String toString() {
        StringBuilder output = new StringBuilder();
        output.append("DecisionStack {\n");
        output.append(String.format("  Livelli: %d, Assegnamenti totali: %d\n",
                procedureStack.size(), getTotalAssignments()));

        // Dettaglio per ogni livello
        for (int levelIndex = 0; levelIndex < procedureStack.size(); levelIndex++) {
            ArrayList<AssignedLiteral> level = procedureStack.get(levelIndex);
            output.append(String.format("\n  Livello %d (%d assegnamenti):\n",
                    levelIndex, level.size()));

            if (level.isEmpty()) {
                output.append("    [vuoto]\n");
                continue;
            }

            // Dettaglio assegnamenti del livello
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

    /**
     * Genera rappresentazione compatta per logging.
     *
     * @return stringa compatta con statistiche essenziali
     */
    public String toCompactString() {
        return String.format("DecisionStack[levels=%d, assignments=%d, current_level_size=%d]",
                procedureStack.size(), getTotalAssignments(),
                procedureStack.isEmpty() ? 0 : procedureStack.peek().size());
    }
}

// ========================================
// CLASSI DI RISULTATO E SUPPORTO
// ========================================

/**
 * Risultato di un'operazione che può generare conflitti.
 *
 * Questa classe encapsula l'esito di operazioni CDCL che possono
 * portare a stati di conflitto, fornendo informazioni dettagliate
 * per la gestione appropriata del flusso algoritmico.
 *
 * Stati Possibili:
 * - Successo senza conflitto
 * - Conflitto con clausola identificata
 * - Progresso con modifiche allo stato
 */
class ConflictResult {

    // ========================================
    // ATTRIBUTI DEL RISULTATO
    // ========================================

    /** Indica se l'operazione ha generato un conflitto */
    private final boolean hasConflict;

    /** Clausola che ha causato il conflitto (null se nessun conflitto) */
    private final List<Integer> conflictClause;

    /** Indica se l'operazione ha prodotto progresso/modifiche */
    private final boolean hasProgress;

    // ========================================
    // COSTRUZIONE
    // ========================================

    /**
     * Costruisce un risultato di conflitto con informazioni complete.
     *
     * @param hasConflict true se si è verificato un conflitto
     * @param conflictClause clausola causante il conflitto (richiesta se hasConflict=true)
     * @param hasProgress true se l'operazione ha modificato lo stato
     */
    public ConflictResult(boolean hasConflict, List<Integer> conflictClause, boolean hasProgress) {
        // Validazione coerenza parametri
        if (hasConflict && (conflictClause == null || conflictClause.isEmpty())) {
            throw new IllegalArgumentException("ConflictClause richiesta quando hasConflict=true");
        }

        this.hasConflict = hasConflict;
        this.conflictClause = conflictClause != null ? new ArrayList<>(conflictClause) : null;
        this.hasProgress = hasProgress;
    }

    // ========================================
    // INTERFACCIA PUBBLICA
    // ========================================

    /** @return true se l'operazione ha generato un conflitto */
    public boolean hasConflict() {
        return hasConflict;
    }

    /** @return clausola di conflitto (copia difensiva) */
    public List<Integer> getConflictClause() {
        return conflictClause != null ? new ArrayList<>(conflictClause) : null;
    }

    /** @return true se l'operazione ha prodotto progresso */
    public boolean hasProgress() {
        return hasProgress;
    }

    // ========================================
    // FACTORY METHODS
    // ========================================

    /** Crea risultato di successo senza conflitto */
    public static ConflictResult success() {
        return new ConflictResult(false, null, true);
    }

    /** Crea risultato di successo senza modifiche */
    public static ConflictResult noProgress() {
        return new ConflictResult(false, null, false);
    }

    /** Crea risultato di conflitto */
    public static ConflictResult conflict(List<Integer> clause) {
        return new ConflictResult(true, clause, true);
    }

    // ========================================
    // UTILITÀ
    // ========================================

    @Override
    public String toString() {
        if (hasConflict) {
            return String.format("ConflictResult{CONFLICT, clause=%s}", conflictClause);
        } else {
            return String.format("ConflictResult{SUCCESS, progress=%s}", hasProgress);
        }
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;

        ConflictResult that = (ConflictResult) obj;
        return hasConflict == that.hasConflict &&
                hasProgress == that.hasProgress &&
                Objects.equals(conflictClause, that.conflictClause);
    }

    @Override
    public int hashCode() {
        return Objects.hash(hasConflict, conflictClause, hasProgress);
    }
}

/**
 * Risultato dell'analisi di un conflitto nell'algoritmo CDCL.
 *
 * Encapsula i risultati del processo di conflict analysis, includendo
 * la clausola appresa e le informazioni per il backtracking.
 */
class ConflictAnalysisResult {

    // ========================================
    // ATTRIBUTI DEL RISULTATO
    // ========================================

    /** Clausola appresa dal processo di analisi */
    private final List<Integer> learnedClause;

    /** Livello di backtrack calcolato per la clausola appresa */
    private final int backtrackLevel;

    // ========================================
    // COSTRUZIONE
    // ========================================

    /**
     * Costruisce un risultato di analisi conflitto.
     *
     * @param learnedClause clausola appresa (può essere vuota per UNSAT)
     * @param backtrackLevel livello di destinazione per backtrack
     */
    public ConflictAnalysisResult(List<Integer> learnedClause, int backtrackLevel) {
        this.learnedClause = learnedClause != null ? new ArrayList<>(learnedClause) : new ArrayList<>();
        this.backtrackLevel = Math.max(-1, backtrackLevel); // -1 indica UNSAT
    }

    // ========================================
    // INTERFACCIA PUBBLICA
    // ========================================

    /** @return clausola appresa (copia difensiva) */
    public List<Integer> getLearnedClause() {
        return new ArrayList<>(learnedClause);
    }

    /** @return livello di backtrack (-1 se UNSAT) */
    public int getBacktrackLevel() {
        return backtrackLevel;
    }

    /** @return true se il risultato indica formula insoddisfacibile */
    public boolean isUnsatisfiable() {
        return backtrackLevel == -1 || learnedClause.isEmpty();
    }

    /** @return true se la clausola appresa è unitaria */
    public boolean isUnitClause() {
        return learnedClause.size() == 1;
    }

    // ========================================
    // FACTORY METHODS
    // ========================================

    /** Crea risultato per clausola appresa normale */
    public static ConflictAnalysisResult learned(List<Integer> clause, int level) {
        return new ConflictAnalysisResult(clause, level);
    }

    /** Crea risultato per formula insoddisfacibile */
    public static ConflictAnalysisResult unsatisfiable() {
        return new ConflictAnalysisResult(new ArrayList<>(), -1);
    }

    // ========================================
    // UTILITÀ
    // ========================================

    @Override
    public String toString() {
        if (isUnsatisfiable()) {
            return "ConflictAnalysisResult{UNSAT}";
        }
        return String.format("ConflictAnalysisResult{clause=%s, backtrack=%d}",
                learnedClause, backtrackLevel);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;

        ConflictAnalysisResult that = (ConflictAnalysisResult) obj;
        return backtrackLevel == that.backtrackLevel &&
                Objects.equals(learnedClause, that.learnedClause);
    }

    @Override
    public int hashCode() {
        return Objects.hash(learnedClause, backtrackLevel);
    }
}