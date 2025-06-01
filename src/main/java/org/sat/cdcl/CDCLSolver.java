package org.sat.cdcl;

import org.sat.cnf.CNFConverter;
import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;

/**
 * Algoritmi Principali:
 * - VSIDS (Variable State Independent Decaying Sum): euristica per la selezione delle variabili
 * - 1UIP (First Unique Implication Point): strategia di apprendimento delle clausole
 * - Non-chronological Backjumping: backtracking basato sui conflitti
 * - Unit Propagation: propagazione delle implicazioni unitarie
 *
 * Flusso Principale dell'algoritmo:
 * - Preprocessing con unit propagation iniziale
 * - Loop principale: Decisione -> Propagazione -> Analisi conflitti -> Salto all'indietro
 * - Terminazione quando tutte le clausole sono soddisfatte o si dimostra insoddisfacibilità
 *
 */
public class CDCLSolver {

    /**
     * Logger per tracciamento dettagliato delle operazioni del solver
     */
    private static final Logger LOGGER = Logger.getLogger(CDCLSolver.class.getName());

    /**
     * Limite massimo di conflitti per prevenire esecuzioni infinite.
     */
    private static final int MAX_CONFLICTS = 1_000_000;

    /**
     * Limite massimo di decisioni per prevenire esecuzioni infinite.
     */
    private static final int MAX_DECISIONS = 1_000_000;

    /**
     * Rappresentazione interna della formula CNF con ottimizzazioni per CDCL
     */
    private final CNFFormula formula;

    /**
     * Stack delle decisioni organizzato per livelli di decisione
     */
    private final DecisionStack decisionStack;

    /**
     * Mappa delle variabili assegnate ordinata secondo euristica VSIDS.
     * La chiave è l'ID della variabile, mentre il valore è l'assegnamento (null se non assegnata).
     */
    private final Map<Integer, AssignedLiteral> assignedValues;

    /**
     * Contatori VSIDS per letterali positivi e negativi.
     * Mantiene la frequenza di apparizione nei conflitti per guidare le decisioni future.
     */
    private final Map<Integer, Integer> vsidsCounter;

    /**
     * Lista delle clausole apprese durante l'analisi dei conflitti
     */
    private final List<List<Integer>> learnedClauses;

    /**
     * Generatore per prove di insoddisfacibilità tramite risoluzione
     */
    private final ProofGenerator proofGenerator;

    /**
     * Collettore di statistiche dettagliate sull'esecuzione del solver
     */
    private final SATStatistics statistics;

    /**
     * Contatore dei conflitti incontrati durante la risoluzione
     */
    private int conflictCount;

    /** Contatore delle decisioni prese durante la risoluzione */
    private int decisionCount;

    /**
     * Clausola che ha causato l'ultimo conflitto.
     * Utilizzata nell'analisi del conflitto per l'apprendimento di nuove clausole.
     */
    private List<Integer> conflictClause;

    /**
     * Flag volatile per gestione sicura delle interruzioni da thread esterni.
     * Utilizzato per implementare timeout controllati.
     */
    private volatile boolean interrupted = false;


    /**
     * Costruisce un nuovo solutore CDCL per la formula CNF specificata.
     *
     * @param cnfConverter formula CNF da risolvere, già convertita in forma normale congiuntiva
     * @throws IllegalArgumentException se la formula è null o malformata
     */
    public CDCLSolver(CNFConverter cnfConverter) {
        LOGGER.info("=== INIZIALIZZAZIONE DEL SOLUTORE CDCL ===");

        // Inizializzazione strutture dati core
        this.formula = new CNFFormula(cnfConverter);
        this.decisionStack = new DecisionStack();
        this.assignedValues = initializeVariableAssignments();
        this.vsidsCounter = initializeVSIDSCounters();

        // Inizializzazione componenti per l'apprendimento di clausole,
        // generazione della prova e delle statistiche
        this.learnedClauses = new ArrayList<>();
        this.proofGenerator = new ProofGenerator();
        this.statistics = new SATStatistics();

        // Inizializzazione stato esecuzione
        this.conflictCount = 0;
        this.decisionCount = 0;
        this.conflictClause = new ArrayList<>();
        this.interrupted = false;

        // Log informazioni formula
        logFormulaInfo();

        LOGGER.info("=== SOLUTORE INIZIALIZZATO CORRETTAMENTE ===");
    }


    /**
     * Questo è il metodo principale che implementa il ciclo CDCL completo
     *
     * @return {@link SATResult} contenente:
     * - Se SAT: assegnamento valido delle variabili
     * - Se UNSAT: prova di insoddisfacibilità
     * - Statistiche dettagliate dell'esecuzione
     *
     * @throws RuntimeException se viene raggiunto il timeout o si verificano errori critici
     */
    public SATResult solve() {
        LOGGER.info("=== INIZIO RISOLUZIONE CDCL ===");

        try {
            // FASE 1: Preprocessing con unit propagation iniziale
            if (!performInitialPreprocessing()) {
                return createUnsatResult("Conflitto durante preprocessing iniziale");
            }

            // FASE 2: Loop principale CDCL
            CDCLLoopResult loopResult = executeCDCLMainLoop();

            // FASE 3: Gestione risultato finale
            return handleFinalResult(loopResult);

        } catch (InterruptedException e) {
            LOGGER.info("Risoluzione interrotta per timeout");
            throw new RuntimeException("Timeout raggiunto durante la risoluzione");

        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Errore critico durante risoluzione CDCL", e);
            statistics.stopTimer();

            if (interrupted || Thread.currentThread().isInterrupted()) {
                throw new RuntimeException("Timeout raggiunto durante la risoluzione");
            }

            throw new RuntimeException("Errore nella risoluzione SAT: " + e.getMessage(), e);
        }
    }

    /**
     * Interrompe la risoluzione in corso (utilizzato per timeout esterni).
     *
     * @apiNote Metodo thread-safe, può essere chiamato da qualsiasi thread
     */
    public void interrupt() {
        this.interrupted = true;
        LOGGER.info("Richiesta interruzione ricevuta - solver verrà fermato");
    }


    /**
     * Esegue il preprocessing iniziale della formula.
     *
     * @return true se la formula è ancora risolvibile dopo preprocessing, false se UNSAT
     */
    private boolean performInitialPreprocessing() {
        LOGGER.fine("Inizio preprocessing iniziale");

        // Unit propagation a livello 0 per clausole unitarie
        PropagationResult initialResult = performLevelZeroUnitPropagation();

        if (initialResult.hasConflict()) {
            LOGGER.info("Conflitto rilevato durante preprocessing - formula UNSAT");
            return false;
        }

        LOGGER.fine("Preprocessing completato con successo");
        return true;
    }

    /**
     * Inizializza la mappa delle variabili con ordinamento VSIDS basato su frequenza.
     *
     * @return mappa ordinata delle variabili con ordinamento VSIDS iniziale
     */
    private LinkedHashMap<Integer, AssignedLiteral> initializeVariableAssignments() {
        LOGGER.fine("Inizializzazione ordinamento VSIDS iniziale");

        // Conta occorrenze di ogni variabile nelle clausole originali
        Map<Integer, Integer> occurrenceFrequency = computeVariableFrequencies();

        // Ordina per frequenza decrescente
        List<Map.Entry<Integer, Integer>> sortedByFrequency = new ArrayList<>(occurrenceFrequency.entrySet());
        sortedByFrequency.sort(Map.Entry.<Integer, Integer>comparingByValue().reversed());

        // Crea mappa ordinata con tutte le variabili non assegnate
        LinkedHashMap<Integer, AssignedLiteral> orderedAssignments = new LinkedHashMap<>();
        for (Map.Entry<Integer, Integer> entry : sortedByFrequency) {
            orderedAssignments.put(entry.getKey(), null); // null: non assegnata
        }

        LOGGER.fine("VSIDS iniziale configurato per " + orderedAssignments.size() + " variabili");
        return orderedAssignments;
    }

    /**
     * Calcola la frequenza di apparizione di ogni variabile nelle clausole originali.
     *
     * @return mappa con frequenza di ogni variabile
     */
    private Map<Integer, Integer> computeVariableFrequencies() {
        Map<Integer, Integer> frequencies = new HashMap<>();

        // Inizializza contatori per tutte le variabili
        for (int var = 1; var <= formula.getVariableCount(); var++) {
            frequencies.put(var, 0);
        }

        // Conta occorrenze nelle clausole
        for (List<Integer> clause : formula.getClauses()) {
            for (Integer literal : clause) {
                int variable = Math.abs(literal);
                frequencies.merge(variable, 1, Integer::sum);
            }
        }

        return frequencies;
    }

    /**
     * Inizializza i contatori VSIDS per tutti i letterali (positivi e negativi).
     *
     * @return mappa dei contatori VSIDS inizializzati a zero
     */
    private Map<Integer, Integer> initializeVSIDSCounters() {
        Map<Integer, Integer> counters = new HashMap<>();

        for (Integer variable : assignedValues.keySet()) {
            counters.put(variable, 0);      // Letterale positivo
            counters.put(-variable, 0);     // Letterale negativo
        }

        LOGGER.fine("Contatori VSIDS inizializzati per " + (counters.size() / 2) + " variabili");
        return counters;
    }

    /**
     * Registra informazioni dettagliate sulla formula caricata.
     */
    private void logFormulaInfo() {
        int clauseCount = formula.getClausesCount();
        int variableCount = formula.getVariableCount();
        double clauseToVarRatio = variableCount > 0 ? (double) clauseCount / variableCount : 0;

        LOGGER.info(String.format("Formula caricata: %d clausole, %d variabili (ratio: %.2f)",
                clauseCount, variableCount, clauseToVarRatio));

        // Log distribuzione lunghezza clausole per diagnostica
        if (LOGGER.isLoggable(Level.FINE)) {
            Map<Integer, Long> lengthDistribution = formula.getClauses().stream()
                    .collect(java.util.stream.Collectors.groupingBy(
                            List::size, java.util.stream.Collectors.counting()));
            LOGGER.fine("Distribuzione lunghezza clausole: " + lengthDistribution);
        }
    }


    /**
     * Esegue il loop principale dell'algoritmo CDCL.
     *
     * @return risultato del loop principale
     * @throws InterruptedException se il solver viene interrotto
     */
    private CDCLLoopResult executeCDCLMainLoop() throws InterruptedException {
        LOGGER.fine("Inizio loop principale CDCL");

        boolean comingFromBacktrack = false;

        while (!problemIsSatisfied() && !interrupted) {
            // Controllo interruzione
            checkForInterruption();

            // Controllo limiti di sicurezza
            if (hasReachedSafetyLimits()) {
                LOGGER.warning("Raggiunti limiti di sicurezza - terminazione forzata");
                return CDCLLoopResult.timeout();
            }

            // STEP 1: Decisione (se non veniamo da backtrack)
            if (!comingFromBacktrack) {
                makeNextDecision();
            } else {
                comingFromBacktrack = false;
            }

            // STEP 2: Unit Propagation
            PropagationResult propagationResult = performUnitPropagation();

            if (!propagationResult.hasConflict()) {
                // Nessun conflitto, continua il loop
                continue;
            }

            // STEP 3: Gestione Conflitto
            ConflictHandlingResult conflictResult = handleConflict(propagationResult.getConflictClause());

            if (conflictResult.isUnsatisfiable()) {
                return CDCLLoopResult.unsat();
            }

            // STEP 4: Backtrack e continua
            performBacktrack(conflictResult.getBacktrackLevel());
            comingFromBacktrack = true;
        }

        // Se si arriva qui, allora la formula è soddisfacibile
        return interrupted ? CDCLLoopResult.interrupted() : CDCLLoopResult.sat();
    }

    /**
     * Controlla se il thread è stato interrotto.
     *
     * @throws InterruptedException se il thread è stato interrotto
     */
    private void checkForInterruption() throws InterruptedException {
        if (Thread.currentThread().isInterrupted() || interrupted) {
            throw new InterruptedException("Solver interrotto");
        }
    }

    /**
     * Verifica se sono stati raggiunti i limiti per l'esecuzione
     *
     * @return true se i limiti sono stati raggiunti
     */
    private boolean hasReachedSafetyLimits() {
        return decisionCount >= MAX_DECISIONS || conflictCount >= MAX_CONFLICTS;
    }


    /**
     * Esegue unit propagation a livello 0 per clausole unitarie.
     *
     * @return risultato della propagazione (conflitto o successo)
     */
    private PropagationResult performLevelZeroUnitPropagation() {
        LOGGER.fine("Unit propagation livello 0 - clausole unitarie originali");

        for (List<Integer> clause : formula.getClauses()) {
            if (clause.size() == 1) {
                Integer literal = clause.get(0);
                Integer variable = Math.abs(literal);
                Boolean value = literal > 0;

                LOGGER.fine("Clausola unitaria trovata: " + variable + " = " + value);

                // Si aggiunge come implicazione a livello 0
                AssignedLiteral assignment = new AssignedLiteral(variable, value, false, clause);
                assignedValues.put(variable, assignment);
                decisionStack.addImpliedLiteral(variable, value, clause);
            }
        }

        // Dopo aver processato le clausole unitarie, esegui propagazione completa
        if (!decisionStack.isEmpty()) {
            return performUnitPropagation();
        }

        return PropagationResult.success();
    }

    /**
     * Esegue unit propagation completa considerando tutte le clausole.
     *
     * @return risultato della propagazione con eventuale clausola di conflitto
     */
    private PropagationResult performUnitPropagation() {
        List<List<Integer>> allClauses = getAllActiveClauses();

        // Loop di propagazione fino a punto fisso o a un conflitto
        for (int clauseIndex = 0; clauseIndex < allClauses.size(); clauseIndex++) {
            List<Integer> clause = allClauses.get(clauseIndex);

            // Analizza stato corrente della clausola
            ClauseEvaluationResult evaluation = evaluateClause(clause);

            switch (evaluation.getStatus()) {
                case SATISFIED:
                    // Clausola già soddisfatta, continua
                    continue;

                case FALSIFIED:
                    // Conflitto rilevato
                    LOGGER.fine("Conflitto in clausola: " + clause);
                    return PropagationResult.conflict(clause);

                case UNIT:
                    // Clausola unitaria: si propaga l'implicazione
                    if (propagateUnitClause(clause, evaluation.getUnitLiteral())) {
                        // Propagazione avvenuta: ricomincia dall'inizio per catturare nuove implicazioni
                        clauseIndex = -1;
                    }
                    break;

                case UNRESOLVED:
                    // Clausola non ancora risolta, quindi continua
                    continue;

                default:
                    throw new IllegalStateException("Status clausola non riconosciuto: " + evaluation.getStatus());
            }
        }

        return PropagationResult.success();
    }

    /**
     * Ottiene tutte le clausole attive (originali + apprese).
     *
     * @return lista di tutte le clausole da considerare nella propagazione
     */
    private List<List<Integer>> getAllActiveClauses() {
        List<List<Integer>> allClauses = new ArrayList<>(formula.getClauses());
        allClauses.addAll(learnedClauses);
        return allClauses;
    }

    /**
     * Valuta lo stato corrente di una clausola rispetto agli assegnamenti attuali.
     *
     * @param clause clausola da valutare
     * @return risultato della valutazione con stato e eventuale letterale unitario
     */
    private ClauseEvaluationResult evaluateClause(List<Integer> clause) {
        int unassignedCount = 0;
        Integer unassignedLiteral = null;

        for (Integer literal : clause) {
            Integer variable = Math.abs(literal);
            AssignedLiteral assignment = assignedValues.get(variable);

            if (assignment == null) {
                // Variabile non assegnata
                unassignedCount++;
                unassignedLiteral = literal;
            } else {
                // Variabile assegnata: controlla se letterale è soddisfatto
                boolean literalValue = assignment.getValue();
                if (literal < 0) {
                    literalValue = !literalValue; // Negazione
                }

                if (literalValue) {
                    // Letterale vero -> clausola soddisfatta
                    return ClauseEvaluationResult.satisfied();
                }
            }
        }

        // Determina stato basato su letterali non assegnati
        if (unassignedCount == 0) {
            return ClauseEvaluationResult.falsified();
        } else if (unassignedCount == 1) {
            return ClauseEvaluationResult.unit(unassignedLiteral);
        } else {
            return ClauseEvaluationResult.unresolved();
        }
    }

    /**
     * Propaga un'implicazione da una clausola unitaria.
     *
     * @param clause clausola unitaria che genera l'implicazione
     * @param unitLiteral letterale che deve essere reso vero
     * @return true se la propagazione è avvenuta, false se la variabile era già assegnata correttamente
     */
    private boolean propagateUnitClause(List<Integer> clause, Integer unitLiteral) {
        Integer variable = Math.abs(unitLiteral);
        Boolean value = unitLiteral > 0;

        // Controlla se la variabile è già assegnata
        AssignedLiteral existingAssignment = assignedValues.get(variable);
        if (existingAssignment != null) {
            // Già assegnata: dovrebbe essere consistente (altrimenti sarebbe conflitto)
            return false;
        }

        // Crea nuova implicazione
        AssignedLiteral newAssignment = new AssignedLiteral(variable, value, false, clause);
        assignedValues.put(variable, newAssignment);
        decisionStack.addImpliedLiteral(variable, value, clause);
        statistics.incrementPropagations();

        LOGGER.fine("Propagazione unit: " + variable + " = " + value + " da " + clause);
        return true;
    }


    /**
     * Prende la prossima decisione usando l'euristica VSIDS.
     * Si seleziona la variabile non assegnata con il punteggio più alto.
     * Il punteggio di una variabile aumenta ogni volta che appare in un conflitto.
     *
     */
    private void makeNextDecision() {
        // Trova la prima variabile non assegnata nell'ordine VSIDS
        for (Map.Entry<Integer, AssignedLiteral> entry : assignedValues.entrySet()) {
            Integer variable = entry.getKey();

            if (entry.getValue() == null) { // Variabile non assegnata
                // Scegli polarità basata su VSIDS counters
                Boolean value = selectVariablePolarity(variable);

                // Crea e registra la decisione
                makeDecision(variable, value);
                return;
            }
        }

        // Non dovremmo mai arrivare qui se problemIsSatisfied() funziona correttamente
        throw new IllegalStateException("Nessuna variabile disponibile per decisione");
    }

    /**
     * Seleziona la polarità (true/false) per una variabile basandosi sui contatori VSIDS.
     *
     * @param variable variabile per cui selezionare la polarità
     * @return true se scegliere polarità positiva, false per negativa
     */
    private Boolean selectVariablePolarity(Integer variable) {
        Integer positiveCount = vsidsCounter.getOrDefault(variable, 0);
        Integer negativeCount = vsidsCounter.getOrDefault(-variable, 0);

        // Scegli la polarità con più conflitti (euristica)
        // In caso di parità, scegli positiva (default)
        return positiveCount >= negativeCount;
    }

    /**
     * Registra una decisione a un nuovo livello di decisione.
     *
     * @param variable variabile da assegnare
     * @param value valore da assegnare alla variabile
     */
    private void makeDecision(Integer variable, Boolean value) {
        // Crea l'assegnamento decisionale
        AssignedLiteral decision = new AssignedLiteral(variable, value, true, null);
        assignedValues.put(variable, decision);
        decisionStack.addDecision(variable, value);

        // Aggiorna contatori
        decisionCount++;
        statistics.incrementDecisions();

        LOGGER.fine(String.format("Decisione: %d = %s @ livello %d (VSIDS: +%d/-%d)",
                variable, value, decisionStack.size() - 1,
                vsidsCounter.get(variable), vsidsCounter.get(-variable)));
    }


    /**
     * Gestisce un conflitto applicando 1UIP.
     *
     * @param conflictClause clausola che ha causato il conflitto
     * @return risultato dell'analisi con livello di backtrack
     */
    private ConflictHandlingResult handleConflict(List<Integer> conflictClause) {
        LOGGER.fine("Inizio analisi conflitto: " + conflictClause);

        // Aggiorna statistiche
        this.conflictClause = new ArrayList<>(conflictClause);
        conflictCount++;
        statistics.incrementConflicts();

        // Aggiorna contatori VSIDS
        updateVSIDSCountersAfterConflict();

        // Esegui analisi First UIP
        ConflictAnalysisResult analysisResult = performFirstUIPAnalysis();

        if (analysisResult.isUnsatisfiable()) {
            LOGGER.info("Formula UNSAT - conflitto irrisolvibile");
            return ConflictHandlingResult.unsatisfiable();
        }

        // Apprendi la nuova clausola
        learnNewClause(analysisResult.getLearnedClause());

        // Calcola livello di backtrack
        int backtrackLevel = analysisResult.getBacktrackLevel();

        LOGGER.fine("Conflitto risolto - backtrack a livello " + backtrackLevel);

        return ConflictHandlingResult.backtrack(backtrackLevel);
    }

    /**
     * Aggiorna i contatori VSIDS dopo un conflitto.
     *
     */
    private void updateVSIDSCountersAfterConflict() {
        for (Integer literal : conflictClause) {
            vsidsCounter.merge(literal, 1, Integer::sum);
        }

        // Riordina le variabili secondo i nuovi punteggi VSIDS
        reorderVariablesByVSIDS();
    }

    /**
     * Riordina la mappa delle variabili secondo i punteggi VSIDS aggiornati.
     *
     */
    private void reorderVariablesByVSIDS() {
        // Crea lista di tutte le entries dei contatori ordinata per punteggio
        List<Map.Entry<Integer, Integer>> sortedCounters = new ArrayList<>(vsidsCounter.entrySet());
        sortedCounters.sort(Map.Entry.<Integer, Integer>comparingByValue().reversed());

        // Si ricostruisce la mappa delle variabili nell'ordine VSIDS
        LinkedHashMap<Integer, AssignedLiteral> reorderedAssignments = new LinkedHashMap<>();

        for (Map.Entry<Integer, Integer> entry : sortedCounters) {
            Integer variable = Math.abs(entry.getKey());

            // Evita duplicati (ogni variabile appare sia come +VAR che -VAR nei contatori)
            if (!reorderedAssignments.containsKey(variable)) {
                reorderedAssignments.put(variable, assignedValues.get(variable));
            }
        }

        // Si sostituisce la mappa con quella riordinata
        assignedValues.clear();
        assignedValues.putAll(reorderedAssignments);

        LOGGER.finest("Variabili riordinate secondo VSIDS aggiornato");
    }

    /**
     * Esegue l'analisi del conflitto con strategia 1UIP.
     *
     * @return risultato dell'analisi con clausola appresa e livello di backtrack
     */
    private ConflictAnalysisResult performFirstUIPAnalysis() {
        List<Integer> currentConflictClause = new ArrayList<>(conflictClause);
        int currentDecisionLevel = decisionStack.size() - 1;

        // Si ottiengono gli assegnamenti del livello corrente per l'analisi
        Map<Integer, AssignedLiteral> currentLevelAssignments = getCurrentLevelAssignments();

        // Loop di risoluzione fino a 1UIP
        while (true) {
            // Conta letterali del livello di decisione corrente nella clausola
            List<Integer> currentLevelLiterals = getCurrentLevelLiterals(currentConflictClause, currentDecisionLevel);

            // 1UIP è raggiunto quando c'è esattamente 1 letterale del livello corrente
            if (currentLevelLiterals.size() <= 1) {
                // Crea la clausola appresa
                List<Integer> learnedClause = new ArrayList<>(currentConflictClause);
                int backtrackLevel = calculateBacktrackLevel(learnedClause);

                return ConflictAnalysisResult.success(learnedClause, backtrackLevel);
            }

            // Trova la migliore clausola per risoluzione
            List<Integer> resolutionClause = findBestResolutionClause(currentConflictClause, currentLevelAssignments);

            if (resolutionClause.isEmpty()) {
                // Non possiamo più proseguire - formula insoddisfacibile
                LOGGER.warning("Impossibile continuare analisi conflitto - UNSAT");
                return ConflictAnalysisResult.unsatisfiable();
            }

            // Si segue la risoluzione binaria
            currentConflictClause = performBinaryResolution(currentConflictClause, resolutionClause);

            // Registra passo per la prova se non troppo voluminosa
            if (proofGenerator.getStepCount() <= 500) {
                proofGenerator.recordResolutionStep(conflictClause, resolutionClause, currentConflictClause);
            }

            // Verifica se abbiamo derivato clausola vuota (UNSAT)
            if (currentConflictClause.isEmpty()) {
                LOGGER.info("Clausola vuota derivata durante analisi - UNSAT");
                return ConflictAnalysisResult.unsatisfiable();
            }
        }
    }

    /**
     * Ottiene gli assegnamenti del livello di decisione corrente.
     *
     * @return mappa degli assegnamenti del livello corrente
     */
    private Map<Integer, AssignedLiteral> getCurrentLevelAssignments() {
        Map<Integer, AssignedLiteral> currentLevel = new HashMap<>();

        for (AssignedLiteral assignment : decisionStack.getTopLevel()) {
            currentLevel.put(assignment.getVariable(), assignment);
        }

        return currentLevel;
    }

    /**
     * Trova i letterali della clausola che appartengono al livello di decisione specificato.
     *
     * @param clause clausola da analizzare
     * @param level livello di decisione di interesse
     * @return lista dei letterali del livello specificato
     */
    private List<Integer> getCurrentLevelLiterals(List<Integer> clause, int level) {
        List<Integer> levelLiterals = new ArrayList<>();

        for (Integer literal : clause) {
            Integer variable = Math.abs(literal);
            AssignedLiteral assignment = assignedValues.get(variable);

            if (assignment != null && getLevelForVariable(variable) == level) {
                levelLiterals.add(literal);
            }
        }

        return levelLiterals;
    }

    /**
     * Ottiene il livello di decisione per una variabile.
     *
     * @param variable variabile di cui trovare il livello
     * @return livello di decisione della variabile
     */
    private int getLevelForVariable(Integer variable) {
        // Cerca la variabile nello stack delle decisioni
        for (int level = 0; level < decisionStack.size(); level++) {
            if (decisionStack.getLiteralsAtLevel(level).contains(variable)) {
                return level;
            }
        }
        return -1; // Non trovata (non dovrebbe succedere)
    }

    /**
     * Trova la migliore clausola per la risoluzione. Si prediligono le clausole che:
     * - Hanno il maggior numero di letterali in comune con la clausola corrente
     * - Sono più corte (meno letterali da aggiungere)
     * - Corrispondono a implicazioni recenti (più vicine nel stack)
     *
     * @param conflictClause clausola corrente di conflitto
     * @param levelAssignments assegnamenti del livello corrente
     * @return clausola migliore per risoluzione
     */
    private List<Integer> findBestResolutionClause(List<Integer> conflictClause,
                                                   Map<Integer, AssignedLiteral> levelAssignments) {
        List<Integer> bestClause = new ArrayList<>();
        int bestScore = Integer.MIN_VALUE;

        for (Integer literal : conflictClause) {
            Integer variable = Math.abs(literal);
            AssignedLiteral assignment = levelAssignments.get(variable);

            // Considera solo implicazioni (non le decisioni)
            if (assignment == null || assignment.isDecision()) {
                continue;
            }

            List<Integer> candidateClause = assignment.getAncestorClause();
            if (candidateClause == null || candidateClause.isEmpty()) {
                continue;
            }

            // Calcola punteggio euristico
            int score = calculateResolutionScore(conflictClause, candidateClause);

            if (score > bestScore) {
                bestScore = score;
                bestClause = new ArrayList<>(candidateClause);
            }
        }

        return bestClause;
    }

    /**
     * Calcola un punteggio euristico per la risoluzione tra due clausole.
     *
     * @param clause1 prima clausola
     * @param clause2 seconda clausola
     * @return punteggio (più alto = migliore)
     */
    private int calculateResolutionScore(List<Integer> clause1, List<Integer> clause2) {
        int score = 0;

        // Penalizza per letterali aggiuntivi che verranno introdotti
        for (Integer literal : clause2) {
            if (!clause1.contains(literal)) {
                score -= 1;
            }
        }

        // Bonus per clausole più corte
        score -= clause2.size();

        return score;
    }

    /**
     * Esegue la risoluzione binaria tra due clausole:
     * rimuove letterali complementari (x e !x) da due clausole e unisce i letterali rimanenti.
     *
     * @param leftClause prima clausola
     * @param rightClause seconda clausola
     * @return clausola risultante dalla risoluzione
     */
    private List<Integer> performBinaryResolution(List<Integer> leftClause, List<Integer> rightClause) {
        // Crea copie per manipolazione
        List<Integer> left = new ArrayList<>(leftClause);
        List<Integer> right = new ArrayList<>(rightClause);

        // Ordina per facilitare la ricerca di complementi
        left.sort(Integer::compareTo);
        right.sort(Integer::compareTo);

        // Trova e rimuovi letterali complementari
        Set<Integer> toRemoveFromLeft = new HashSet<>();
        Set<Integer> toRemoveFromRight = new HashSet<>();

        for (Integer leftLiteral : left) {
            Integer complement = -leftLiteral;
            if (right.contains(complement)) {
                toRemoveFromLeft.add(leftLiteral);
                toRemoveFromRight.add(complement);
            }
        }

        // Rimuovi letterali complementari
        left.removeAll(toRemoveFromLeft);
        right.removeAll(toRemoveFromRight);

        // Unisci le clausole rimanenti (evitando duplicati)
        Set<Integer> resolvent = new HashSet<>(left);
        resolvent.addAll(right);

        return new ArrayList<>(resolvent);
    }

    /**
     * Calcola il livello di backtrack per una clausola appresa.
     *
     * @param learnedClause clausola appresa
     * @return livello di backtrack appropriato
     */
    private int calculateBacktrackLevel(List<Integer> learnedClause) {
        if (learnedClause.isEmpty()) {
            return -1; // Clausola vuota = UNSAT
        }

        if (learnedClause.size() == 1) {
            return 0; // Clausola unitaria = backtrack al livello 0
        }

        // Raccoglie tutti i livelli dei letterali nella clausola
        List<Integer> levels = new ArrayList<>();

        for (Integer literal : learnedClause) {
            Integer variable = Math.abs(literal);
            int level = getLevelForVariable(variable);
            if (level >= 0) {
                levels.add(level);
            }
        }

        if (levels.size() < 2) {
            return 0; // Fallback sicuro
        }

        // Ordina in ordine decrescente e prendi il secondo più alto
        levels.sort(Collections.reverseOrder());
        return levels.get(1);
    }

    /**
     * Apprende una nuova clausola e gestisce la memoria.
     *
     * @param learnedClause clausola da apprendere
     */
    private void learnNewClause(List<Integer> learnedClause) {
        // Evita duplicati
        if (!formula.getClauses().contains(learnedClause) && !learnedClauses.contains(learnedClause)) {

            // Gestione memoria: rimuovi clausole vecchie se necessario
            manageLearnedClausesMemory();

            // Aggiungi la nuova clausola
            learnedClauses.add(new ArrayList<>(learnedClause));
            statistics.incrementLearnedClauses();

            LOGGER.fine("Clausola appresa: " + learnedClause + " (totale: " + learnedClauses.size() + ")");
        }
    }

    /**
     * Quando il numero di clausole apprese diventa troppo grande, rimuove
     * le clausole più grandi per mantenere l'uso di memoria sotto controllo.
     */
    private void manageLearnedClausesMemory() {
        int maxLearnedClauses = formula.getClausesCount() / 3;

        if (learnedClauses.size() >= maxLearnedClauses) {
            // Ordina per dimensione decrescente
            learnedClauses.sort((c1, c2) -> Integer.compare(c2.size(), c1.size()));

            // Rimuove il 30% delle clausole più grandi
            int toRemove = Math.max(1, learnedClauses.size() / 3);

            for (int i = 0; i < toRemove && !learnedClauses.isEmpty(); i++) {
                learnedClauses.remove(0);
            }

            LOGGER.fine("Forgetting: rimosse " + toRemove + " clausole apprese (memoria)");
        }
    }


    /**
     * Esegue backtrack non cronologico, andando direttamente al
     * livello dove la clausola appresa diventa unitaria.
     *
     * @param targetLevel livello di destinazione del backtrack
     */
    private void performBacktrack(int targetLevel) {
        int currentLevel = decisionStack.size() - 1;

        LOGGER.fine("Backtrack non cronologico: livello " + currentLevel + " → " + targetLevel);

        // Identifica il letterale di asserzione per dopo il backtrack
        AssertionInfo assertionInfo = determineAssertionLiteral();

        // Rimuovi tutti i livelli sopra il target
        while (decisionStack.size() > targetLevel + 1) {
            List<AssignedLiteral> removedLevel = decisionStack.deleteLevel();

            // Rimuovi gli assegnamenti delle variabili del livello rimosso
            for (AssignedLiteral assignment : removedLevel) {
                assignedValues.put(assignment.getVariable(), null);
            }
        }

        // Aggiungi il letterale di asserzione come implicazione al nuovo livello
        if (assertionInfo.isValid()) {
            addAssertionAfterBacktrack(assertionInfo);
        }

        // Aggiorna statistiche
        statistics.incrementBackjumps();

        LOGGER.fine("Backtrack completato - nuovo livello: " + (decisionStack.size() - 1));
    }

    /**
     * Determina il letterale di asserzione dalla clausola di conflitto.
     *
     * @return informazioni sul letterale di asserzione
     */
    private AssertionInfo determineAssertionLiteral() {
        // Il letterale di asserzione è tipicamente quello che rende vera la clausola appresa
        for (Integer literal : conflictClause) {
            Integer variable = Math.abs(literal);
            AssignedLiteral currentAssignment = assignedValues.get(variable);

            if (currentAssignment != null) {
                Boolean assertionValue = determineAssertionValue(literal, currentAssignment);
                return new AssertionInfo(variable, assertionValue, conflictClause);
            }
        }

        return AssertionInfo.invalid();
    }

    /**
     * Determina il valore di asserzione per un letterale.
     *
     * @param literal letterale originale
     * @param currentAssignment assegnamento corrente
     * @return valore di asserzione
     */
    private Boolean determineAssertionValue(Integer literal, AssignedLiteral currentAssignment) {
        boolean isNegated = literal < 0;
        boolean currentValue = currentAssignment.getValue();

        // L'asserzione dovrebbe rendere il letterale vero
        return isNegated ? !currentValue : currentValue;
    }

    /**
     * Aggiunge il letterale di asserzione dopo il backtrack.
     *
     * @param assertionInfo informazioni sul letterale di asserzione
     */
    private void addAssertionAfterBacktrack(AssertionInfo assertionInfo) {
        AssignedLiteral assertion = new AssignedLiteral(
                assertionInfo.getVariable(),
                assertionInfo.getValue(),
                false, // È un'implicazione, non una decisione
                assertionInfo.getSourceClause()
        );

        assignedValues.put(assertionInfo.getVariable(), assertion);
        decisionStack.addImpliedLiteral(
                assertionInfo.getVariable(),
                assertionInfo.getValue(),
                assertionInfo.getSourceClause()
        );

        LOGGER.fine("Asserzione dopo backtrack: " + assertionInfo.getVariable() +
                " = " + assertionInfo.getValue());
    }


    /**
     * Verifica se il problema è completamente soddisfatto.
     *
     * @return true se la formula è completamente soddisfatta
     */
    private boolean problemIsSatisfied() {
        // Verifica clausole originali
        if (!areAllClausesSatisfied(formula.getClauses())) {
            return false;
        }

        // Verifica clausole apprese
        if (!areAllClausesSatisfied(learnedClauses)) {
            return false;
        }

        // Se si arriva qui, allora tutte le clausole sono soddisfatte
        return true;
    }

    /**
     * Verifica se tutte le clausole in una lista sono soddisfatte.
     *
     * @param clauses lista di clausole da verificare
     * @return true se tutte sono soddisfatte
     */
    private boolean areAllClausesSatisfied(List<List<Integer>> clauses) {
        for (List<Integer> clause : clauses) {
            ClauseEvaluationResult evaluation = evaluateClause(clause);

            switch (evaluation.getStatus()) {
                case SATISFIED:
                    continue; // Clausola OK

                case FALSIFIED:
                    LOGGER.warning("Clausola falsificata rilevata: " + clause);
                    return false;

                case UNIT:
                case UNRESOLVED:
                    // Ci sono ancora clausole incomplete
                    return false;

                default:
                    throw new IllegalStateException("Status clausola non riconosciuto");
            }
        }

        return true;
    }

    /**
     * Genera il modello finale per una formula soddisfacibile.
     *
     * @return mappa con l'assegnamento completo delle variabili usando i nomi originali
     */
    private Map<String, Boolean> generateModel() {
        Map<String, Boolean> model = new HashMap<>();

        LOGGER.fine("Generazione modello finale con nomi variabili originali");

        // Ottieni il mapping inverso: da ID numerico a nome variabile
        Map<Integer, String> inverseMapping = createInverseVariableMapping();

        for (int variable = 1; variable <= formula.getVariableCount(); variable++) {
            AssignedLiteral assignment = assignedValues.get(variable);

            // Ottieni il nome originale della variabile
            String originalVariableName = inverseMapping.get(variable);
            if (originalVariableName == null) {
                // Fallback: usa l'ID numerico se non trovato
                originalVariableName = String.valueOf(variable);
                LOGGER.warning("Nome originale non trovato per variabile " + variable);
            }

            if (assignment != null) {
                // Variabile assegnata durante la ricerca
                model.put(originalVariableName, assignment.getValue());
                LOGGER.finest("Modello: " + originalVariableName + " = " + assignment.getValue() +
                        " (" + (assignment.isDecision() ? "decisione" : "implicazione") + ")");
            } else {
                // Variabile non assegnata - usa valore di default
                model.put(originalVariableName, true);
                LOGGER.finest("Modello: " + originalVariableName + " = true (default)");
            }
        }

        LOGGER.info("Modello generato con " + model.size() + " variabili usando nomi originali");
        return model;
    }

    /**
     * Crea il mapping inverso da ID numerico a nome variabile originale.
     *
     * @return mappa che associa ogni ID numerico al nome originale della variabile
     */
    private Map<Integer, String> createInverseVariableMapping() {
        Map<Integer, String> inverseMapping = new HashMap<>();
        Map<String, Integer> originalMapping = formula.getVariableMapping();

        // Inverti il mapping: da (nome -> ID) a (ID -> nome)
        for (Map.Entry<String, Integer> entry : originalMapping.entrySet()) {
            inverseMapping.put(entry.getValue(), entry.getKey());
        }

        LOGGER.fine("Mapping inverso creato: " + inverseMapping);
        return inverseMapping;
    }


    /**
     * Gestisce il risultato finale del loop CDCL.
     *
     * @param loopResult risultato del loop principale
     * @return risultato SAT finale
     */
    private SATResult handleFinalResult(CDCLLoopResult loopResult) {
        statistics.stopTimer();

        switch (loopResult.getType()) {
            case SAT:
                LOGGER.info("Formula SAT - generazione modello finale");
                Map<String, Boolean> model = generateModel();
                return SATResult.satisfiable(model, statistics);

            case UNSAT:
                LOGGER.info("Formula UNSAT - generazione prova");
                String proof = proofGenerator.generateProof();
                statistics.setProofSize(proofGenerator.getStepCount());
                return SATResult.unsatisfiable(proof, statistics);

            case TIMEOUT:
                LOGGER.warning("Risoluzione terminata per limite iterazioni");
                throw new RuntimeException("Timeout raggiunto durante la risoluzione");

            case INTERRUPTED:
                LOGGER.info("Risoluzione interrotta esternamente");
                throw new RuntimeException("Solver interrotto per timeout");

            default:
                throw new IllegalStateException("Tipo di risultato non gestito: " + loopResult.getType());
        }
    }

    /**
     * Crea un risultato UNSAT con la prova appropriata.
     *
     * @param reason motivo dell'insoddisfacibilità
     * @return risultato UNSAT
     */
    private SATResult createUnsatResult(String reason) {
        statistics.stopTimer();
        LOGGER.info("Formula UNSAT: " + reason);
        return SATResult.unsatisfiable(proofGenerator.generateProof(), statistics);
    }

    /**
     * Ottiene le statistiche parziali correnti del solutore.
     *
     * @return statistiche parziali correnti
     */
    public SATStatistics getPartialStatistics() {
        // Non fermare il timer se il solutore è ancora in esecuzione
        SATStatistics partialStats = new SATStatistics();

        // Copia i contatori attuali
        partialStats.incrementDecisions(); // Aggiorna con i valori correnti
        for (int i = 0; i < decisionCount; i++) {
            partialStats.incrementDecisions();
        }

        for (int i = 0; i < conflictCount; i++) {
            partialStats.incrementConflicts();
        }

        // Per le altre statistiche, copia dal statistics object corrente
        partialStats.setProofSize(proofGenerator.getStepCount());

        return partialStats;
    }

    // ========================================
    // CLASSI DI SUPPORTO INTERNE DEL SOLUTORE
    // ========================================

    /**
     * Risultato della propagazione unitaria.
     */
    private static class PropagationResult {
        private final boolean hasConflict;
        private final List<Integer> conflictClause;

        private PropagationResult(boolean hasConflict, List<Integer> conflictClause) {
            this.hasConflict = hasConflict;
            this.conflictClause = conflictClause;
        }

        public boolean hasConflict() { return hasConflict; }
        public List<Integer> getConflictClause() { return conflictClause; }

        public static PropagationResult success() {
            return new PropagationResult(false, null);
        }

        public static PropagationResult conflict(List<Integer> clause) {
            return new PropagationResult(true, clause);
        }
    }

    /**
     * Risultato della valutazione di una clausola.
     */
    private static class ClauseEvaluationResult {
        public enum Status { SATISFIED, FALSIFIED, UNIT, UNRESOLVED }

        private final Status status;
        private final Integer unitLiteral;

        private ClauseEvaluationResult(Status status, Integer unitLiteral) {
            this.status = status;
            this.unitLiteral = unitLiteral;
        }

        public Status getStatus() { return status; }
        public Integer getUnitLiteral() { return unitLiteral; }

        public static ClauseEvaluationResult satisfied() {
            return new ClauseEvaluationResult(Status.SATISFIED, null);
        }

        public static ClauseEvaluationResult falsified() {
            return new ClauseEvaluationResult(Status.FALSIFIED, null);
        }

        public static ClauseEvaluationResult unit(Integer literal) {
            return new ClauseEvaluationResult(Status.UNIT, literal);
        }

        public static ClauseEvaluationResult unresolved() {
            return new ClauseEvaluationResult(Status.UNRESOLVED, null);
        }
    }

    /**
     * Informazioni sul letterale di asserzione dopo backtrack.
     */
    private static class AssertionInfo {
        private final Integer variable;
        private final Boolean value;
        private final List<Integer> sourceClause;
        private final boolean valid;

        private AssertionInfo(Integer variable, Boolean value, List<Integer> sourceClause) {
            this.variable = variable;
            this.value = value;
            this.sourceClause = sourceClause;
            this.valid = true;
        }

        private AssertionInfo() {
            this.variable = null;
            this.value = null;
            this.sourceClause = null;
            this.valid = false;
        }

        public Integer getVariable() { return variable; }
        public Boolean getValue() { return value; }
        public List<Integer> getSourceClause() { return sourceClause; }
        public boolean isValid() { return valid; }

        public static AssertionInfo invalid() { return new AssertionInfo(); }
    }

    /**
     * Risultato dell'analisi del conflitto.
     */
    private static class ConflictAnalysisResult {
        private final List<Integer> learnedClause;
        private final int backtrackLevel;
        private final boolean unsatisfiable;

        private ConflictAnalysisResult(List<Integer> learnedClause, int backtrackLevel, boolean unsatisfiable) {
            this.learnedClause = learnedClause;
            this.backtrackLevel = backtrackLevel;
            this.unsatisfiable = unsatisfiable;
        }

        public List<Integer> getLearnedClause() { return learnedClause; }
        public int getBacktrackLevel() { return backtrackLevel; }
        public boolean isUnsatisfiable() { return unsatisfiable; }

        public static ConflictAnalysisResult success(List<Integer> clause, int level) {
            return new ConflictAnalysisResult(clause, level, false);
        }

        public static ConflictAnalysisResult unsatisfiable() {
            return new ConflictAnalysisResult(null, -1, true);
        }
    }

    /**
     * Risultato della gestione del conflitto.
     */
    private static class ConflictHandlingResult {
        private final boolean unsatisfiable;
        private final int backtrackLevel;

        private ConflictHandlingResult(boolean unsatisfiable, int backtrackLevel) {
            this.unsatisfiable = unsatisfiable;
            this.backtrackLevel = backtrackLevel;
        }

        public boolean isUnsatisfiable() { return unsatisfiable; }
        public int getBacktrackLevel() { return backtrackLevel; }

        public static ConflictHandlingResult unsatisfiable() {
            return new ConflictHandlingResult(true, -1);
        }

        public static ConflictHandlingResult backtrack(int level) {
            return new ConflictHandlingResult(false, level);
        }
    }

    /**
     * Risultato del loop principale CDCL.
     */
    private static class CDCLLoopResult {
        public enum Type { SAT, UNSAT, TIMEOUT, INTERRUPTED }

        private final Type type;
        private final Map<String, Boolean> model;
        private final String proof;

        private CDCLLoopResult(Type type, Map<String, Boolean> model, String proof) {
            this.type = type;
            this.model = model;
            this.proof = proof;
        }

        public Type getType() { return type; }
        public Map<String, Boolean> getModel() { return model; }
        public String getProof() { return proof; }

        public static CDCLLoopResult sat() {
            return new CDCLLoopResult(Type.SAT, null, null);
        }

        public static CDCLLoopResult satWithModel(Map<String, Boolean> model) {
            return new CDCLLoopResult(Type.SAT, model, null);
        }

        public static CDCLLoopResult unsat() {
            return new CDCLLoopResult(Type.UNSAT, null, null);
        }

        public static CDCLLoopResult unsatWithProof(String proof) {
            return new CDCLLoopResult(Type.UNSAT, null, proof);
        }

        public static CDCLLoopResult timeout() {
            return new CDCLLoopResult(Type.TIMEOUT, null, null);
        }

        public static CDCLLoopResult interrupted() {
            return new CDCLLoopResult(Type.INTERRUPTED, null, null);
        }
    }
}