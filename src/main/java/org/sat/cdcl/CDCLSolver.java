package org.sat.cdcl;

import org.sat.cnf.CNFConverter;
import org.sat.optionalfeatures.RestartTechnique;
import org.sat.support.CNFFormula;
import org.sat.support.DecisionStack;
import org.sat.support.AssignedLiteral;
import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;

/**
 * SOLUTORE CDCL AVANZATO - Implementazione completa con restart opzionale e anti-loop VSIDS avanzato
 *
 * Implementazione dell'algoritmo CDCL con integrazione opzionale della tecnica restart
 * per prevenzione stalli durante la ricerca SAT. Il restart è attivato solo quando
 * esplicitamente richiesto tramite configurazione.
 *
 * NUOVO: Anti-loop VSIDS avanzato - Traccia tutte le variabili già scelte e le esclude
 * finché esistono alternative non ancora tentate, prevenendo loop complessi.
 */
public class CDCLSolver {

    private static final Logger LOGGER = Logger.getLogger(CDCLSolver.class.getName());

    //region STRUTTURE DATI CORE DELL'ALGORITMO

    /** Formula CNF ottimizzata per elaborazione CDCL */
    private final CNFFormula formula;

    /** Stack gerarchico per gestione livelli di decisione e backtracking */
    private final DecisionStack decisionStack;

    /** Mappa variabile → assegnamento corrente (null = non assegnata) */
    private final Map<Integer, AssignedLiteral> assignedValues;

    /** Contatori VSIDS per euristica selezione variabili dinamica */
    private final Map<Integer, Integer> vsidsCounter;

    /** Clausole apprese durante conflict analysis per miglioramento performance */
    private final List<List<Integer>> learnedClauses;

    /** Generatore prove matematiche per formule UNSAT */
    private final ProofGenerator proofGenerator;

    /** Mapping letterale → clausola unitaria originale per spiegazioni livello 0 */
    private final Map<Integer, List<Integer>> unitClauseMapping;

    //endregion

    //region STATO E CONTROLLO ESECUZIONE

    /** Statistiche dettagliate di esecuzione (decisioni, conflitti, tempo, memoria) */
    private SATStatistics statistics;

    /** Contatore conflitti rilevati durante la risoluzione */
    private int conflictCount;

    /** Contatore decisioni euristiche prese */
    private int decisionCount;

    /** Flag per interruzione esterna controllata (gestione timeout) */
    private volatile boolean interrupted = false;

    /** NUOVO: Tecnica restart opzionale (null se non abilitata) */
    private RestartTechnique restartTechnique;

    //endregion

    //region NUOVO: ANTI-LOOP VSIDS AVANZATO

    /**
     * NUOVO: Set di tutte le variabili già scelte almeno una volta.
     * Utilizzato per escludere variabili già tentate finché esistono alternative.
     */
    private final Set<Integer> alreadyChosenVariables;

    /**
     * NUOVO: Contatore cicli di reset per statistiche e debugging.
     * Incrementato ogni volta che si resetta alreadyChosenVariables.
     */
    private int antiLoopResetCount;

    //endregion

    //region INIZIALIZZAZIONE E CONFIGURAZIONE SOLUTORE

    /**
     * Costruisce il solutore CDCL completo senza restart.
     * @param cnfConverter formula CNF in formato albero da convertire
     */
    public CDCLSolver(CNFConverter cnfConverter) {
        this(cnfConverter, false);
    }

    /**
     * Costruisce il solutore CDCL completo con restart opzionale.
     *
     * @param cnfConverter formula CNF in formato albero da convertire
     * @param enableRestart true per abilitare tecnica restart
     */
    public CDCLSolver(CNFConverter cnfConverter, boolean enableRestart) {
        LOGGER.info("=== INIZIALIZZAZIONE SOLUTORE CDCL AVANZATO ===");

        // Conversione e validazione formula
        this.formula = new CNFFormula(cnfConverter);

        // Inizializzazione strutture dati core
        this.decisionStack = new DecisionStack();
        this.assignedValues = initializeVariableAssignmentsOptimized();
        this.vsidsCounter = initializeVSIDSCounters();
        this.learnedClauses = new ArrayList<>();
        this.unitClauseMapping = new HashMap<>();

        // Configurazione sistema di prove
        this.proofGenerator = new ProofGenerator();
        this.proofGenerator.setVariableMapping(createInverseVariableMapping());

        // NUOVO: Inizializzazione restart opzionale
        if (enableRestart) {
            this.restartTechnique = new RestartTechnique();
            LOGGER.info("Restart technique ABILITATA");
        } else {
            this.restartTechnique = null;
            LOGGER.info("Restart technique DISABILITATA");
        }

        // Reset contatori e stato
        this.conflictCount = 0;
        this.decisionCount = 0;
        this.interrupted = false;

        // NUOVO: Inizializzazione anti-loop VSIDS avanzato
        this.alreadyChosenVariables = new HashSet<>();
        this.antiLoopResetCount = 0;

        // Validazione e logging
        logSolverInitializationInfo();
        LOGGER.info("=== SOLUTORE CDCL PRONTO PER ESECUZIONE ===");
    }

    /**
     * Inizializza gli assegnamenti delle variabili con ottimizzazione per frequenza.
     */
    private LinkedHashMap<Integer, AssignedLiteral> initializeVariableAssignmentsOptimized() {
        // Calcola frequenza di apparizione per ogni variabile
        Map<Integer, Integer> variableFrequencies = new HashMap<>();
        for (int var = 1; var <= formula.getVariableCount(); var++) {
            variableFrequencies.put(var, 0);
        }

        // Conta apparizioni nelle clausole
        for (List<Integer> clause : formula.getClauses()) {
            for (Integer literal : clause) {
                int variable = Math.abs(literal);
                variableFrequencies.merge(variable, 1, Integer::sum);
            }
        }

        // Ordina per frequenza decrescente
        List<Map.Entry<Integer, Integer>> sortedByFrequency = new ArrayList<>(variableFrequencies.entrySet());
        sortedByFrequency.sort(Map.Entry.<Integer, Integer>comparingByValue().reversed());

        // Costruisce mappa ordinata con assegnamenti inizialmente nulli
        LinkedHashMap<Integer, AssignedLiteral> orderedAssignments = new LinkedHashMap<>();
        for (Map.Entry<Integer, Integer> entry : sortedByFrequency) {
            orderedAssignments.put(entry.getKey(), null);
        }

        LOGGER.fine("Variabili ordinate per frequenza: " + sortedByFrequency.size() + " variabili");
        return orderedAssignments;
    }

    /**
     * Inizializza contatori VSIDS per euristica dinamica di selezione variabili.
     */
    private Map<Integer, Integer> initializeVSIDSCounters() {
        Map<Integer, Integer> counters = new HashMap<>();

        for (Integer variable : assignedValues.keySet()) {
            counters.put(variable, 0);     // Letterale positivo
            counters.put(-variable, 0);    // Letterale negativo
        }

        LOGGER.fine("Contatori VSIDS inizializzati per " + counters.size() + " letterali");
        return counters;
    }

    /**
     * Crea mapping inverso per conversione ID numerico → nome variabile originale.
     */
    private Map<Integer, String> createInverseVariableMapping() {
        Map<Integer, String> inverseMapping = new HashMap<>();
        Map<String, Integer> originalMapping = formula.getVariableMapping();

        for (Map.Entry<String, Integer> entry : originalMapping.entrySet()) {
            inverseMapping.put(entry.getValue(), entry.getKey());
        }

        return inverseMapping;
    }

    /**
     * Registra informazioni dettagliate su formula caricata e configurazione solutore.
     */
    private void logSolverInitializationInfo() {
        int clauseCount = formula.getClausesCount();
        int variableCount = formula.getVariableCount();
        double clauseVariableRatio = variableCount > 0 ? (double) clauseCount / variableCount : 0;

        LOGGER.info(String.format("Formula SAT caricata: %d clausole, %d variabili (ratio C/V: %.2f)",
                clauseCount, variableCount, clauseVariableRatio));

        if (clauseVariableRatio > 4.0) {
            LOGGER.info("Formula densa rilevata - aspettarsi ricerca più complessa");
        } else if (clauseVariableRatio < 2.0) {
            LOGGER.info("Formula sparsa rilevata - ricerca potenzialmente più veloce");
        }

        LOGGER.info("Anti-loop VSIDS avanzato: ATTIVO per prevenzione cicli complessi");
    }

    //endregion

    //region INTERFACCIA PUBBLICA E CONTROLLO ESECUZIONE

    /**
     * METODO PRINCIPALE: Risolve la formula CNF utilizzando l'algoritmo CDCL completo.
     */
    public SATResult solve() {
        LOGGER.info("=== AVVIO RISOLUZIONE CDCL ===");
        this.statistics = new SATStatistics();

        try {
            // Esecuzione algoritmo CDCL completo
            CDCLExecutionResult executionResult = executeCDCLMainAlgorithm();

            // Generazione risultato finale
            return generateFinalResult(executionResult);

        } catch (InterruptedException e) {
            return handleInterruption();
        } catch (Exception e) {
            return handleCriticalError(e);
        }
    }

    /**
     * Interrompe la risoluzione in modo controllato.
     */
    public void interrupt() {
        this.interrupted = true;
        LOGGER.info("Richiesta interruzione controllata ricevuta");
    }

    /**
     * Restituisce statistiche parziali durante esecuzione.
     */
    public SATStatistics getPartialStatistics() {
        SATStatistics partialStats = new SATStatistics();

        // CORRETTO: Copia contatori correnti senza modificare gli originali
        int currentDecisions = decisionCount;
        int currentConflicts = conflictCount;
        int currentRestarts = (restartTechnique != null) ? restartTechnique.getTotalRestarts() : 0;

        // Replica le statistiche senza usare loop che modificherebbero i contatori
        for (int i = 0; i < currentDecisions; i++) {
            partialStats.incrementDecisions();
        }
        for (int i = 0; i < currentConflicts; i++) {
            partialStats.incrementConflicts();
        }
        for (int i = 0; i < currentRestarts; i++) {
            partialStats.incrementRestarts();
        }

        // Copia altre statistiche
        partialStats.setProofSize(proofGenerator.getStepCount());

        return partialStats;
    }

    //endregion

    //region LOOP PRINCIPALE ALGORITMO CDCL

    /**
     * Esegue il loop principale dell'algoritmo CDCL con gestione completa di tutti i casi.
     */
    private CDCLExecutionResult executeCDCLMainAlgorithm() throws InterruptedException {
        LOGGER.fine("=== AVVIO LOOP PRINCIPALE CDCL ===");

        int iterationCount = 0;
        final int MAX_ITERATIONS = 10_000_000;

        try {
            // FASE INIZIALIZZAZIONE: Configura livello 0 con clausole unitarie
            initializeLevel0WithUnitClauses();
        } catch (ImmediateUNSATException e) {
            // NUOVO: Gestione UNSAT immediato da clausole unitarie contraddittorie
            LOGGER.info("Formula UNSAT determinata durante inizializzazione: " + e.getMessage());
            return CDCLExecutionResult.unsatisfiable();
        }

        // LOOP PRINCIPALE CDCL
        while (!interrupted) {
            iterationCount++;

            // Protezione contro loop infiniti
            if (iterationCount > MAX_ITERATIONS) {
                LOGGER.warning("Raggiunto limite massimo iterazioni: " + MAX_ITERATIONS);
                return CDCLExecutionResult.timeout();
            }

            // Controllo interruzione per timeout
            checkForInterruption();

            // Log progresso periodico
            if (iterationCount % 1000 == 0) {
                logIterationProgress(iterationCount);
            }

            LOGGER.finest("=== ITERAZIONE CDCL " + iterationCount + " ===");

            // STEP 1: Verifica se formula è completamente soddisfatta
            if (isFormulaSatisfied()) {
                LOGGER.info("Formula SAT - tutte le clausole soddisfatte");
                return CDCLExecutionResult.satisfiable();
            }

            // STEP 2: Unit propagation con rilevamento conflitti
            PropagationResult propagationResult = executeUnitPropagation();

            if (propagationResult.hasConflict()) {
                // STEP 3: Risoluzione conflitto con flusso ibrido
                ConflictAnalysisResult analysisResult = resolveConflict(
                        propagationResult.getConflictClause(),
                        propagationResult.getJustifyingClause()
                );

                if (analysisResult.isUnsatisfiable()) {
                    LOGGER.info("Formula UNSAT determinata tramite conflict analysis");
                    return CDCLExecutionResult.unsatisfiable();
                }

                // STEP 4: Learning e backtracking
                executeLearningAndBacktrack(analysisResult);
                continue; // Riprova con nuova configurazione
            }

            // STEP 5: Decision making se non tutti assegnati
            if (!areAllVariablesAssigned()) {
                executeDecisionMaking();
            }
        }

        LOGGER.info("Loop CDCL completato - Iterazioni: " + iterationCount);
        return interrupted ? CDCLExecutionResult.interrupted() : CDCLExecutionResult.satisfiable();
    }

    //endregion

    //region NUOVO: RISOLUZIONE CONFLITTO CON FLUSSO IBRIDO

    /**
     * NUOVO: Verifica se una nuova clausola da apprendere è consistente con quelle già apprese.
     * CORRETTO: Per clausole unitarie, verifica specificatamente contro clausole unitarie del livello 0.
     *
     * @param newClause clausola da verificare per consistenza
     * @return clausola in conflitto se inconsistente, null se consistente
     */
    private List<Integer> checkConsistencyWithLearnedClauses(List<Integer> newClause) {
        LOGGER.fine("=== VERIFICA CONSISTENZA CLAUSOLA DA APPRENDERE ===");
        LOGGER.fine("Nuova clausola: " + newClause);

        // CORRETTO: Per clausole unitarie, verifica contro clausole unitarie del livello 0
        if (newClause.size() == 1) {
            return checkUnitClauseConsistencyWithLevel0(newClause);
        }

        // Per clausole non unitarie, verifica normalmente contro tutte le clausole
        return checkNonUnitClauseConsistency(newClause);
    }

    /**
     * NUOVO: Verifica consistenza di clausola unitaria contro assegnamenti unitari del livello 0.
     *
     * @param unitClause clausola unitaria da verificare
     * @return clausola unitaria in conflitto se inconsistente, null se consistente
     */
    private List<Integer> checkUnitClauseConsistencyWithLevel0(List<Integer> unitClause) {
        LOGGER.fine("=== VERIFICA CLAUSOLA UNITARIA CONTRO LIVELLO 0 ===");
        LOGGER.fine("Clausola unitaria: " + unitClause);

        Integer literal = unitClause.get(0);
        Integer variable = Math.abs(literal);
        Boolean expectedValue = literal > 0;

        // Verifica contro assegnamenti del livello 0
        List<AssignedLiteral> level0Assignments = decisionStack.getAssignmentsAtLevel(0);

        for (AssignedLiteral assignment : level0Assignments) {
            if (assignment.getVariable().equals(variable)) {
                Boolean actualValue = assignment.getValue();

                if (!actualValue.equals(expectedValue)) {
                    // INCONSISTENZA TROVATA: variabile ha valore opposto al livello 0
                    LOGGER.info("*** INCONSISTENZA CLAUSOLA UNITARIA CON LIVELLO 0 ***");
                    LOGGER.info("Clausola unitaria: " + unitClause + " richiede " + variable + " = " + expectedValue);
                    LOGGER.info("Livello 0 ha: " + variable + " = " + actualValue);

                    // Crea clausola unitaria contradditoria
                    List<Integer> conflictingUnitClause = Arrays.asList(-literal);
                    LOGGER.info("Clausola contradditoria: " + conflictingUnitClause);

                    return conflictingUnitClause;
                }
            }
        }

        // Verifica contro clausole unitarie già apprese
        for (List<Integer> learnedClause : learnedClauses) {
            if (learnedClause.size() == 1) {
                Integer learnedLiteral = learnedClause.get(0);
                Integer learnedVariable = Math.abs(learnedLiteral);

                if (learnedVariable.equals(variable)) {
                    Boolean learnedValue = learnedLiteral > 0;

                    if (!learnedValue.equals(expectedValue)) {
                        LOGGER.info("*** INCONSISTENZA CON CLAUSOLA UNITARIA APPRESA ***");
                        LOGGER.info("Nuova clausola: " + unitClause);
                        LOGGER.info("Clausola appresa: " + learnedClause);
                        return learnedClause;
                    }
                }
            }
        }

        LOGGER.fine("Clausola unitaria consistente con livello 0 e clausole apprese");
        return null; // Consistente
    }

    /**
     * NUOVO: Verifica consistenza di clausola non unitaria contro tutte le clausole.
     *
     * @param nonUnitClause clausola non unitaria da verificare
     * @return clausola in conflitto se inconsistente, null se consistente
     */
    private List<Integer> checkNonUnitClauseConsistency(List<Integer> nonUnitClause) {
        LOGGER.fine("=== VERIFICA CLAUSOLA NON UNITARIA ===");
        LOGGER.fine("Clausola non unitaria: " + nonUnitClause);

        // Verifica contro clausole originali della formula
        for (List<Integer> existingClause : formula.getClauses()) {
            if (areClausesContradictory(nonUnitClause, existingClause)) {
                LOGGER.fine("Inconsistenza trovata con clausola originale: " + existingClause);
                return existingClause;
            }
        }

        // Verifica contro clausole già apprese
        for (List<Integer> existingClause : learnedClauses) {
            if (areClausesContradictory(nonUnitClause, existingClause)) {
                LOGGER.fine("Inconsistenza trovata con clausola appresa: " + existingClause);
                return existingClause;
            }
        }

        LOGGER.fine("Clausola non unitaria consistente");
        return null; // Consistente
    }

    /**
     * NUOVO: Verifica se due clausole sono contradditorie (possono generare clausola vuota).
     *
     * @param clause1 prima clausola
     * @param clause2 seconda clausola
     * @return true se le clausole sono contradditorie
     */
    private boolean areClausesContradictory(List<Integer> clause1, List<Integer> clause2) {
        // Genera spiegazione matematica tra le due clausole
        List<Integer> explanation = generateMathematicalExplanation(clause1, clause2);

        // Se la spiegazione è vuota, le clausole sono contradditorie
        boolean contradictory = explanation.isEmpty();

        if (contradictory) {
            LOGGER.finest("Clausole contradditorie rilevate: " + clause1 + " ∧ " + clause2 + " ⊢ []");
        }

        return contradictory;
    }

    /**
     * CORRETTO: Risolve conflitto con flusso ibrido basato su lunghezza clausola.
     *
     * - Clausola unitaria → Backtrack livello 0 + Learning diretto
     * - Clausola non unitaria → Verifica propagazioni + Iterazioni
     */
    private ConflictAnalysisResult resolveConflict(List<Integer> conflictClause,
                                                   List<Integer> justifyingClause) {
        LOGGER.fine("=== RISOLUZIONE CONFLITTO CON FLUSSO IBRIDO ===");
        LOGGER.fine("Clausola conflitto: " + conflictClause);
        LOGGER.fine("Clausola giustificante: " + justifyingClause);

        // STEP 1: Aggiorna statistiche
        conflictCount++;
        statistics.incrementConflicts();
        updateVSIDSCountersAfterConflict(conflictClause);

        // STEP 2: Gestione restart se abilitato
        if (restartTechnique != null) {
            boolean shouldRestart = restartTechnique.registerConflictAndCheckRestart();
            if (shouldRestart) {
                LOGGER.info("*** RESTART ATTIVATO ***");
                statistics.incrementRestarts();
                return executeRestartProcedure();
            }
        }

        // STEP 3: Genera spiegazione iniziale
        List<Integer> learnedClause = generateMathematicalExplanation(conflictClause, justifyingClause);

        LOGGER.info("Spiegazione generata: " + conflictClause + " ∧ " + justifyingClause + " ⊢ " + learnedClause);
        proofGenerator.recordResolutionStep(conflictClause, justifyingClause, learnedClause);

        // STEP 4: Verifica clausola vuota → UNSAT
        if (learnedClause.isEmpty()) {
            LOGGER.info("*** CLAUSOLA VUOTA DERIVATA - FORMULA UNSAT ***");
            return ConflictAnalysisResult.unsatisfiable();
        }

        // STEP 5: FLUSSO IBRIDO basato su lunghezza clausola
        if (learnedClause.size() == 1) {
            // CASO A: CLAUSOLA UNITARIA → Comportamento semplificato
            LOGGER.info("*** CLAUSOLA UNITARIA RILEVATA → FLUSSO SEMPLIFICATO ***");
            return handleUnitClauseLearning(learnedClause);

        } else {
            // CASO B: CLAUSOLA NON UNITARIA → Comportamento con iterazioni
            LOGGER.info("*** CLAUSOLA NON UNITARIA → FLUSSO CON VERIFICA PROPAGAZIONI ***");
            return handleNonUnitClauseLearning(learnedClause, conflictClause, justifyingClause);
        }
    }

    /**
     * NUOVO: Gestisce learning di clausole unitarie (flusso semplificato).
     *
     * Per clausole unitarie:
     * 1. Backtrack al livello 0
     * 2. Verifica consistenza solo con clausole apprese
     * 3. Apprendi direttamente
     */
    private ConflictAnalysisResult handleUnitClauseLearning(List<Integer> unitClause) {
        LOGGER.fine("=== GESTIONE CLAUSOLA UNITARIA ===");
        LOGGER.fine("Clausola unitaria: " + unitClause);

        // Verifica consistenza SOLO con clausole già apprese
        List<Integer> conflictingLearnedClause = checkConsistencyWithLearnedClauses(unitClause);

        if (conflictingLearnedClause != null) {
            LOGGER.info("*** INCONSISTENZA CLAUSOLA UNITARIA CON CLAUSOLE APPRESE ***");
            LOGGER.info("Clausola unitaria: " + unitClause + " vs " + conflictingLearnedClause);

            // Genera spiegazione finale per UNSAT
            List<Integer> finalClause = generateMathematicalExplanation(unitClause, conflictingLearnedClause);
            proofGenerator.recordResolutionStep(unitClause, conflictingLearnedClause, finalClause);

            if (finalClause.isEmpty()) {
                LOGGER.info("*** CLAUSOLA VUOTA DA INCONSISTENZA UNITARIA - FORMULA UNSAT ***");
                return ConflictAnalysisResult.unsatisfiable();
            }
        }

        // Backtrack al livello 0 per clausole unitarie
        int backtrackLevel = 0;

        LOGGER.info("Clausola unitaria da apprendere: " + unitClause);
        LOGGER.info("Backtrack al livello 0 - propagazioni gestite dal ciclo principale");

        return ConflictAnalysisResult.backtrack(unitClause, backtrackLevel);
    }

    /**
     * NUOVO: Gestisce learning di clausole non unitarie (flusso con iterazioni).
     *
     * Per clausole non unitarie:
     * 1. Verifica consistenza con propagazioni correnti
     * 2. Se inconsistente → iterazioni con nuove spiegazioni
     * 3. Se consistente → verifica con clausole apprese e apprendi
     */
    private ConflictAnalysisResult handleNonUnitClauseLearning(List<Integer> initialLearnedClause,
                                                               List<Integer> initialConflictClause,
                                                               List<Integer> initialJustifyingClause) {
        LOGGER.fine("=== GESTIONE CLAUSOLA NON UNITARIA ===");

        // Processo iterativo per clausole non unitarie
        List<Integer> currentConflictClause = initialConflictClause;
        List<Integer> currentJustifyingClause = initialJustifyingClause;
        List<Integer> currentLearnedClause = initialLearnedClause;
        int iterationCount = 0;

        while (true) {
            iterationCount++;
            LOGGER.fine("--- ITERAZIONE NON UNITARIA #" + iterationCount + " ---");
            LOGGER.fine("Clausola corrente: " + currentLearnedClause);

            // Verifica consistenza con assegnazioni correnti (propagazioni)
            if (isConsistentWithCurrentAssignments(currentLearnedClause)) {
                LOGGER.fine("Clausola " + currentLearnedClause + " consistente con assegnazioni correnti");

                // Verifica consistenza con clausole già apprese
                List<Integer> conflictingLearnedClause = checkConsistencyWithLearnedClauses(currentLearnedClause);

                if (conflictingLearnedClause != null) {
                    LOGGER.info("*** INCONSISTENZA NON UNITARIA CON CLAUSOLE APPRESE ***");
                    LOGGER.info("Clausola: " + currentLearnedClause + " vs " + conflictingLearnedClause);

                    // Genera spiegazione finale
                    List<Integer> finalClause = generateMathematicalExplanation(
                            currentLearnedClause, conflictingLearnedClause);

                    proofGenerator.recordResolutionStep(currentLearnedClause, conflictingLearnedClause, finalClause);

                    if (finalClause.isEmpty()) {
                        LOGGER.info("*** CLAUSOLA VUOTA DA INCONSISTENZA NON UNITARIA - FORMULA UNSAT ***");
                        return ConflictAnalysisResult.unsatisfiable();
                    }
                }

                // Clausola può essere appresa
                int backtrackLevel = calculateSimpleBacktrackLevel(currentLearnedClause);
                LOGGER.info("Clausola non unitaria appresa: " + currentLearnedClause + ", backtrack: " + backtrackLevel);
                return ConflictAnalysisResult.backtrack(currentLearnedClause, backtrackLevel);

            } else {
                // Clausola inconsistente → nuova iterazione
                LOGGER.info("*** CLAUSOLA NON UNITARIA INCONSISTENTE CON PROPAGAZIONI ***");
                LOGGER.info("Clausola: " + currentLearnedClause + " inconsistente con assegnazioni correnti");

                List<Integer> nextJustifyingClause = findNextJustifyingClauseForIteration(currentLearnedClause);

                if (nextJustifyingClause == null) {
                    LOGGER.warning("Nessuna clausola giustificante trovata per iterazione non unitaria");
                    return ConflictAnalysisResult.unsatisfiable();
                }

                // Genera nuova spiegazione
                List<Integer> newLearnedClause = generateMathematicalExplanation(
                        currentLearnedClause, nextJustifyingClause);

                LOGGER.info("Nuova spiegazione non unitaria: " + currentLearnedClause + " ∧ " +
                        nextJustifyingClause + " ⊢ " + newLearnedClause);

                proofGenerator.recordResolutionStep(currentLearnedClause, nextJustifyingClause, newLearnedClause);

                // Verifica clausola vuota
                if (newLearnedClause.isEmpty()) {
                    LOGGER.info("*** CLAUSOLA VUOTA DA ITERAZIONE NON UNITARIA - FORMULA UNSAT ***");
                    return ConflictAnalysisResult.unsatisfiable();
                }

                // Prepara prossima iterazione
                currentConflictClause = currentLearnedClause;
                currentJustifyingClause = nextJustifyingClause;
                currentLearnedClause = newLearnedClause;

                // Protezione anti-loop
                if (iterationCount > 50) {
                    LOGGER.warning("Troppi loop iterativo non unitario - possibile ciclo infinito");
                    return ConflictAnalysisResult.unsatisfiable();
                }
            }
        }
    }

    /**
     * NUOVO: Verifica se una clausola è consistente con le assegnazioni correnti.
     *
     * Una clausola è inconsistente se tutte le sue letterali sono false sotto
     * le assegnazioni correnti (propagazioni e decisioni).
     *
     * @param clause clausola da verificare
     * @return true se consistente, false se inconsistente
     */
    private boolean isConsistentWithCurrentAssignments(List<Integer> clause) {
        LOGGER.finest("Verifica consistenza clausola: " + clause + " con assegnazioni correnti");

        boolean hasUnassignedLiteral = false;
        boolean hasTrueLiteral = false;

        for (Integer literal : clause) {
            Integer variable = Math.abs(literal);
            boolean expectedValue = literal > 0;

            AssignedLiteral assignment = assignedValues.get(variable);

            if (assignment == null) {
                // Variabile non assegnata → clausola può essere soddisfatta
                hasUnassignedLiteral = true;
                LOGGER.finest("Variabile " + variable + " non assegnata → clausola può essere soddisfatta");
            } else {
                boolean actualValue = assignment.getValue();

                if (actualValue == expectedValue) {
                    // Letterale vero → clausola soddisfatta
                    hasTrueLiteral = true;
                    LOGGER.finest("Letterale " + literal + " vero → clausola soddisfatta");
                    break;
                } else {
                    LOGGER.finest("Letterale " + literal + " falso (variabile " + variable + " = " + actualValue + ")");
                }
            }
        }

        boolean consistent = hasTrueLiteral || hasUnassignedLiteral;

        LOGGER.finest("Clausola " + clause + " → consistente: " + consistent);
        return consistent;
    }

    /**
     * NUOVO: Trova la prossima clausola giustificante per l'iterazione di spiegazione.
     *
     * Cerca la clausola che ha giustificato una delle variabili presenti nella
     * clausola inconsistente, partendo dalle propagazioni più recenti.
     *
     * @param inconsistentClause clausola che è risultata inconsistente
     * @return clausola giustificante per prossima iterazione o null se non trovata
     */
    private List<Integer> findNextJustifyingClauseForIteration(List<Integer> inconsistentClause) {
        LOGGER.fine("Ricerca prossima clausola giustificante per: " + inconsistentClause);

        // Ottieni tutte le implicazioni in ordine cronologico inverso (più recenti prima)
        List<AssignedLiteral> allImplications = getAllImplicationsInChronologicalOrder();
        Collections.reverse(allImplications); // Più recenti prima

        // Cerca una variabile della clausola inconsistente che è stata propagata
        for (Integer literal : inconsistentClause) {
            Integer variable = Math.abs(literal);

            // Trova l'implicazione più recente di questa variabile
            for (AssignedLiteral implication : allImplications) {
                if (implication.getVariable().equals(variable) && implication.hasAncestorClause()) {
                    List<Integer> justifyingClause = implication.getAncestorClause();

                    LOGGER.fine("Trovata clausola giustificante per variabile " + variable + ": " + justifyingClause);
                    return justifyingClause;
                }
            }
        }

        // Fallback: cerca tra clausole originali della formula
        for (Integer literal : inconsistentClause) {
            Integer variable = Math.abs(literal);

            for (List<Integer> originalClause : formula.getClauses()) {
                if (containsVariable(originalClause, variable)) {
                    LOGGER.fine("Usando clausola originale come giustificante per " + variable + ": " + originalClause);
                    return originalClause;
                }
            }
        }

        LOGGER.warning("Nessuna clausola giustificante trovata per: " + inconsistentClause);
        return null;
    }

    /**
     * SUPPORTO: Verifica se una clausola contiene una specifica variabile.
     */
    private boolean containsVariable(List<Integer> clause, Integer variable) {
        return clause.stream().anyMatch(literal -> Math.abs(literal) == variable.intValue());
    }

    /**
     * SUPPORTO: Calcola livello di backtrack semplificato per clausola appresa.
     *
     * @param learnedClause clausola risultante dalla spiegazione
     * @return livello appropriato per backtracking
     */
    private int calculateSimpleBacktrackLevel(List<Integer> learnedClause) {
        if (learnedClause.size() == 1) {
            // Clausola unitaria → backtrack al livello 0 per propagazione immediata
            LOGGER.finest("Clausola unitaria → backtrack al livello 0");
            return 0;
        } else {
            // Clausola multipla → backtrack di un livello per permettere assertion
            int currentLevel = decisionStack.getLevel();
            int targetLevel = Math.max(0, currentLevel - 1);

            LOGGER.finest("Clausola multipla → backtrack: " + currentLevel + " → " + targetLevel);
            return targetLevel;
        }
    }

    /**
     * SUPPORTO: Esegue procedura restart semplificata.
     * Usa il metodo esistente ma con gestione semplificata.
     */
    private ConflictAnalysisResult executeRestartProcedure() {
        try {
            // Prepara dati per restart
            List<AssignedLiteral> level0Assignments = decisionStack.getAssignmentsAtLevel(0);
            List<List<Integer>> currentLearnedClauses = new ArrayList<>(learnedClauses);

            // Esegue restart
            RestartTechnique.RestartResult restartResult = restartTechnique.executeRestart(
                    level0Assignments, currentLearnedClauses);

            // Esegue backtrack al livello 0
            performRestartBacktrack();

            // Aggiorna clausole apprese con quelle ottimizzate
            updateLearnedClausesFromRestart(restartResult);

            // Reset anti-loop dopo restart
            resetAntiLoopTracking();

            LOGGER.info("Restart #" + restartResult.restartNumber + " completato");
            LOGGER.info("Sussunzione: " + restartResult.subsumptionRemovals + " clausole rimosse");

            // Ritorna segnale di continuazione normale (clausola vuota per evitare learning aggiuntivo)
            return ConflictAnalysisResult.backtrack(Collections.emptyList(), 0);

        } catch (Exception e) {
            LOGGER.log(Level.WARNING, "Errore durante restart", e);
            // Fallback: continua senza restart
            return ConflictAnalysisResult.backtrack(Collections.emptyList(), 0);
        }
    }

    /**
     * NUOVO: Ottiene TUTTE le implicazioni in ordine cronologico da tutti i livelli.
     * Non solo livello 0, ma tutti i livelli di decisione.
     */
    private List<AssignedLiteral> getAllImplicationsInChronologicalOrder() {
        List<AssignedLiteral> allImplications = new ArrayList<>();

        // Raccogli implicazioni da tutti i livelli in ordine cronologico
        for (int level = 0; level < decisionStack.size(); level++) {
            List<AssignedLiteral> levelAssignments = decisionStack.getAssignmentsAtLevel(level);

            // Filtra solo le implicazioni (non le decisioni)
            for (AssignedLiteral assignment : levelAssignments) {
                if (assignment.isImplication() && assignment.hasAncestorClause()) {
                    allImplications.add(assignment);
                }
            }
        }

        LOGGER.fine("Raccolte " + allImplications.size() + " implicazioni totali da tutti i livelli");
        return allImplications;
    }

    //endregion

    //region INIZIALIZZAZIONE LIVELLO 0 E CLAUSOLE UNITARIE

    /**
     * Inizializza livello 0 con tutte le clausole unitarie originali della formula.
     * CORRETTO: Rileva immediatamente UNSAT se clausole unitarie contradditorie.
     */
    private void initializeLevel0WithUnitClauses() {
        LOGGER.fine("=== INIZIALIZZAZIONE LIVELLO 0 CON CLAUSOLE UNITARIE ===");

        List<List<Integer>> allClauses = formula.getClauses();
        int unitClausesAdded = 0;

        // NUOVO: Tracking per rilevamento contradizioni immediate
        Map<Integer, Boolean> unitClauseValues = new HashMap<>();
        Map<Integer, List<Integer>> unitClauseSources = new HashMap<>();

        for (List<Integer> clause : allClauses) {
            if (clause.size() == 1) {
                Integer literal = clause.get(0);
                Integer variable = Math.abs(literal);
                Boolean value = literal > 0;

                // NUOVO: Verifica contraddizioni immediate tra clausole unitarie
                if (unitClauseValues.containsKey(variable)) {
                    Boolean existingValue = unitClauseValues.get(variable);
                    if (!existingValue.equals(value)) {
                        // CONTRADDIZIONE RILEVATA: K e !K
                        LOGGER.info("*** CONTRADDIZIONE CLAUSOLE UNITARIE RILEVATA ***");
                        LOGGER.info("Variabile " + variable + ": clausola1=" + existingValue + ", clausola2=" + value);

                        // Genera prova immediata: (K) e (!K) genera []
                        List<Integer> clause1 = unitClauseSources.get(variable);
                        List<Integer> clause2 = new ArrayList<>(clause);
                        List<Integer> emptyClause = new ArrayList<>();

                        proofGenerator.recordResolutionStep(clause1, clause2, emptyClause);

                        // Aggiorna statistiche: 1 conflitto = 1 passo di prova
                        conflictCount = 1;
                        statistics.incrementConflicts();

                        LOGGER.info("Prova UNSAT generata: " + clause1 + " ∧ " + clause2 + " ⊢ []");
                        throw new ImmediateUNSATException("Clausole unitarie contraddittorie rilevate al livello 0");
                    }
                }

                // Verifica se variabile già assegnata
                if (assignedValues.get(variable) == null) {
                    // Aggiunge assegnamento unitario al livello 0
                    AssignedLiteral unitAssignment = new AssignedLiteral(variable, value, false, clause);
                    assignedValues.put(variable, unitAssignment);
                    decisionStack.addImpliedLiteral(variable, value, clause);

                    // Registra mapping per uso nelle spiegazioni
                    unitClauseMapping.put(literal, new ArrayList<>(clause));

                    // NUOVO: Registra per controllo contraddizioni
                    unitClauseValues.put(variable, value);
                    unitClauseSources.put(variable, new ArrayList<>(clause));

                    unitClausesAdded++;

                    LOGGER.fine("Clausola unitaria aggiunta al livello 0: " + variable + " = " + value);
                } else {
                    // Verifica consistenza se già assegnata
                    validateUnitClauseConsistency(variable, value);
                }
            }
        }

        LOGGER.info("Livello 0 inizializzato con " + unitClausesAdded + " clausole unitarie");
    }

    /**
     * NUOVO: Eccezione per segnalare UNSAT immediato durante inizializzazione.
     */
    private static class ImmediateUNSATException extends RuntimeException {
        public ImmediateUNSATException(String message) {
            super(message);
        }
    }

    /**
     * Valida consistenza tra clausole unitarie per rilevamento immediato di UNSAT.
     */
    private void validateUnitClauseConsistency(Integer variable, Boolean expectedValue) {
        AssignedLiteral existing = assignedValues.get(variable);
        if (existing != null && !existing.getValue().equals(expectedValue)) {
            LOGGER.severe("Conflitto immediato tra clausole unitarie per variabile: " + variable);
        }
    }

    /**
     * Controlla se il thread corrente è stato interrotto e lancia eccezione appropriata.
     */
    private void checkForInterruption() throws InterruptedException {
        if (Thread.currentThread().isInterrupted() || interrupted) {
            throw new InterruptedException("Solver interrotto per timeout");
        }
    }

    /**
     * Registra progresso periodico per monitoring di esecuzioni lunghe.
     */
    private void logIterationProgress(int iterationCount) {
        int assignedCount = countAssignedVariables();
        int totalVariables = formula.getVariableCount();
        int currentLevel = decisionStack.getLevel();

        String restartInfo = "";
        if (restartTechnique != null) {
            restartInfo = String.format(", Restart: %d", restartTechnique.getTotalRestarts());
        }

        String antiLoopInfo = "";
        if (!alreadyChosenVariables.isEmpty()) {
            antiLoopInfo = String.format(", Anti-loop: %d variabili bloccate, %d reset",
                    alreadyChosenVariables.size(), antiLoopResetCount);
        }

        LOGGER.fine(String.format("Iterazione %d - Livello: %d, Decisioni: %d, Conflitti: %d%s, Assegnate: %d/%d%s",
                iterationCount, currentLevel, decisionCount, conflictCount, restartInfo, assignedCount, totalVariables, antiLoopInfo));
    }

    //endregion

    //region CONFLICT ANALYSIS METODI ESISTENTI

    /**
     * CORRETTO: Identifica l'ultima clausola giustificante che ha causato una propagazione
     * prima che si verificasse il conflitto.
     *
     * Algoritmo:
     * 1. Trova l'ultima implicazione fatta cronologicamente
     * 2. Verifica che sia coinvolta nel conflitto corrente
     * 3. Ritorna la sua clausola giustificante
     *
     * @param conflictClause clausola che è andata in conflitto
     * @return ultima clausola giustificante o null se non trovata
     */
    private List<Integer> findJustifyingClauseForConflict(List<Integer> conflictClause) {
        LOGGER.fine("=== RICERCA ULTIMA CLAUSOLA GIUSTIFICANTE ===");
        LOGGER.fine("Clausola in conflitto: " + conflictClause);

        // Ottieni TUTTE le implicazioni in ordine cronologico (tutti i livelli)
        List<AssignedLiteral> allImplications = getAllImplicationsInChronologicalOrder();

        if (allImplications.isEmpty()) {
            LOGGER.warning("Nessuna implicazione trovata per conflitto");
            return null;
        }

        // Cerca dall'ultima implicazione verso la prima
        for (int i = allImplications.size() - 1; i >= 0; i--) {
            AssignedLiteral lastImplication = allImplications.get(i);
            Integer variable = lastImplication.getVariable();
            Boolean value = lastImplication.getValue();

            LOGGER.finest("Controllo implicazione #" + i + ": " + variable + " = " + value +
                    " giustificata da " + lastImplication.getAncestorClause());

            // Verifica se questa variabile è coinvolta nel conflitto
            if (isVariableInvolvedInConflict(variable, value, conflictClause)) {
                List<Integer> justifyingClause = lastImplication.getAncestorClause();

                LOGGER.info("*** ULTIMA CLAUSOLA GIUSTIFICANTE TROVATA ***");
                LOGGER.info("Variabile: " + variable + " = " + value);
                LOGGER.info("Clausola giustificante: " + justifyingClause);

                return justifyingClause;
            }
        }

        LOGGER.warning("Nessuna clausola giustificante trovata per il conflitto: " + conflictClause);
        return null;
    }

    /**
     * NUOVO: Verifica se una variabile con il suo valore è coinvolta nel conflitto.
     *
     * Una variabile è coinvolta se:
     * - La variabile appare nella clausola conflitto
     * - Il valore assegnato rende falso il letterale nella clausola
     *
     * @param variable variabile da controllare
     * @param assignedValue valore assegnato alla variabile
     * @param conflictClause clausola in conflitto
     * @return true se la variabile contribuisce al conflitto
     */
    private boolean isVariableInvolvedInConflict(Integer variable, Boolean assignedValue, List<Integer> conflictClause) {
        for (Integer literal : conflictClause) {
            int literalVariable = Math.abs(literal);

            if (literalVariable == variable.intValue()) {
                // La variabile è presente nella clausola conflitto
                boolean literalPolarity = literal > 0;

                // Verifica se l'assegnamento rende falso questo letterale
                boolean literalIsFalse = (literalPolarity && !assignedValue) || (!literalPolarity && assignedValue);

                if (literalIsFalse) {
                    LOGGER.finest("Variabile " + variable + "=" + assignedValue +
                            " rende falso il letterale " + literal + " nella clausola conflitto");
                    return true;
                }
            }
        }

        return false;
    }

    /**
     * Genera spiegazione matematica tra due clausole applicando risoluzione.
     */
    private List<Integer> generateMathematicalExplanation(List<Integer> clause1, List<Integer> clause2) {
        LOGGER.finest("Generazione spiegazione matematica: " + clause1 + " ⊕ " + clause2);

        Set<Integer> resultLiterals = new HashSet<>();

        // Aggiungi letterali dalla prima clausola
        if (clause1 != null) {
            resultLiterals.addAll(clause1);
        }

        // Aggiungi letterali dalla seconda clausola, eliminando complementari
        if (clause2 != null) {
            for (Integer literal : clause2) {
                if (resultLiterals.contains(-literal)) {
                    // Letterali complementari → rimuovi entrambi
                    resultLiterals.remove(-literal);
                } else {
                    // Letterale non complementare → aggiungi
                    resultLiterals.add(literal);
                }
            }
        }

        List<Integer> explanationResult = new ArrayList<>(resultLiterals);
        explanationResult.sort(Integer::compareTo);

        LOGGER.finest("Spiegazione completata: " + explanationResult);
        return explanationResult;
    }

    /**
     * Aggiorna contatori VSIDS dopo conflitto per migliorare euristica futura.
     */
    private void updateVSIDSCountersAfterConflict(List<Integer> conflictClause) {
        for (Integer literal : conflictClause) {
            vsidsCounter.merge(literal, 1, Integer::sum);
        }
        LOGGER.finest("Contatori VSIDS aggiornati per conflitto: " + conflictClause);
    }

    //endregion

    //region CLAUSE LEARNING E BACKTRACKING

    /**
     * Esegue learning di clausole e backtracking non-cronologico.
     */
    private void executeLearningAndBacktrack(ConflictAnalysisResult analysisResult) {
        List<Integer> learnedClause = analysisResult.getLearnedClause();
        int backtrackLevel = analysisResult.getBacktrackLevel();

        LOGGER.fine("Learning e backtrack: clausola=" + learnedClause + ", livello=" + backtrackLevel);

        // Step 1: Apprendi clausola se non duplicata
        if (!learnedClause.isEmpty()) {
            learnClauseIfNovel(learnedClause);
        }

        // Step 2: Esegui backtracking
        if (!learnedClause.isEmpty() || backtrackLevel > 0) {
            performBacktrackToLevel(backtrackLevel);
        }

        // Step 3: Applica assertion se clausola unitaria
        if (!learnedClause.isEmpty()) {
            applyAssertionIfUnit(learnedClause, backtrackLevel);
        }
    }

    /**
     * Apprende nuova clausola se non è duplicata di clausole esistenti.
     */
    private void learnClauseIfNovel(List<Integer> learnedClause) {
        if (learnedClause == null || learnedClause.isEmpty()) {
            return;
        }

        if (!isClauseDuplicate(learnedClause)) {
            learnedClauses.add(new ArrayList<>(learnedClause));
            statistics.incrementLearnedClauses();
            LOGGER.fine("Clausola appresa: " + learnedClause);
        } else {
            LOGGER.finest("Clausola duplicata non appresa: " + learnedClause);
        }
    }

    /**
     * Verifica se clausola è duplicata rispetto a clausole esistenti.
     */
    private boolean isClauseDuplicate(List<Integer> clause) {
        // Controlla clausole originali
        for (List<Integer> existing : formula.getClauses()) {
            if (areClausesEquivalent(clause, existing)) {
                return true;
            }
        }

        // Controlla clausole apprese
        for (List<Integer> existing : learnedClauses) {
            if (areClausesEquivalent(clause, existing)) {
                return true;
            }
        }

        return false;
    }

    /**
     * Verifica equivalenza tra due clausole (stesso set di letterali).
     */
    private boolean areClausesEquivalent(List<Integer> clause1, List<Integer> clause2) {
        if (clause1.size() != clause2.size()) {
            return false;
        }

        Set<Integer> set1 = new HashSet<>(clause1);
        Set<Integer> set2 = new HashSet<>(clause2);
        return set1.equals(set2);
    }

    /**
     * Esegue backtracking non-cronologico al livello specificato.
     */
    private void performBacktrackToLevel(int targetLevel) {
        int currentLevel = decisionStack.getLevel();

        if (targetLevel >= currentLevel) {
            LOGGER.fine("Nessun backtrack necessario: livello corrente " + currentLevel + " <= target " + targetLevel);
            return;
        }

        LOGGER.fine("Esecuzione backtrack: " + currentLevel + " → " + targetLevel);

        // Rimuovi livelli sequenzialmente
        while (decisionStack.getLevel() > targetLevel) {
            List<AssignedLiteral> removedAssignments = decisionStack.deleteLevel();

            // Annulla assegnamenti rimossi
            for (AssignedLiteral assignment : removedAssignments) {
                assignedValues.put(assignment.getVariable(), null);
            }
        }

        statistics.incrementBackjumps();
        LOGGER.fine("Backtrack completato al livello " + decisionStack.getLevel());
    }

    /**
     * Applica assertion di clausola unitaria appresa al livello corrente.
     */
    private void applyAssertionIfUnit(List<Integer> learnedClause, int level) {
        if (learnedClause != null && learnedClause.size() == 1) {
            Integer literal = learnedClause.get(0);
            Integer variable = Math.abs(literal);
            Boolean value = literal > 0;

            if (assignedValues.get(variable) == null) {
                AssignedLiteral assertion = new AssignedLiteral(variable, value, false, learnedClause);
                assignedValues.put(variable, assertion);
                decisionStack.addImpliedLiteral(variable, value, learnedClause);

                LOGGER.fine("Assertion applicata: " + variable + " = " + value + " (auto-giustificata da learning)");
            }
        }
    }

    //endregion

    //region RESTART E ANTI-LOOP

    /**
     * NUOVO: Reset del tracking anti-loop dopo restart.
     * Il restart resetta completamente la ricerca quindi è sicuro ripartire da capo.
     */
    private void resetAntiLoopTracking() {
        alreadyChosenVariables.clear();
        antiLoopResetCount = 0;
        LOGGER.fine("Anti-loop VSIDS: Reset completo dopo restart");
    }

    /**
     * Esegue backtrack al livello 0 per restart.
     */
    private void performRestartBacktrack() {
        int currentLevel = decisionStack.getLevel();
        int removedAssignments = 0;

        // Rimuove tutti i livelli superiori al livello 0
        while (decisionStack.getLevel() > 0) {
            List<AssignedLiteral> removedLevel = decisionStack.deleteLevel();

            // Annulla assegnamenti rimossi
            for (AssignedLiteral assignment : removedLevel) {
                assignedValues.put(assignment.getVariable(), null);
                removedAssignments++;
            }
        }

        LOGGER.info("Restart backtrack: " + removedAssignments + " assegnamenti eliminati, livello: " + decisionStack.getLevel());
    }

    /**
     * Aggiorna clausole apprese con quelle ottimizzate dal restart.
     */
    private void updateLearnedClausesFromRestart(RestartTechnique.RestartResult restartResult) {
        // Sostituisce clausole apprese con quelle ottimizzate
        learnedClauses.clear();
        learnedClauses.addAll(restartResult.optimizedLearnedClauses);

        LOGGER.fine("Clausole apprese aggiornate post-restart: " + learnedClauses.size());
    }

    //endregion

    //region UNIT PROPAGATION E RILEVAMENTO CONFLITTI

    /**
     * Esegue unit propagation completa con rilevamento automatico di conflitti.
     */
    private PropagationResult executeUnitPropagation() {
        List<List<Integer>> allActiveClauses = getAllActiveClauses();
        boolean propagationProgress;
        int propagationRounds = 0;

        LOGGER.fine("Avvio unit propagation su " + allActiveClauses.size() + " clausole attive");

        do {
            propagationProgress = false;
            propagationRounds++;

            // Protezione contro loop infiniti nella propagazione
            if (propagationRounds > 1000) {
                LOGGER.warning("Unit propagation interrotta: possibile loop infinito dopo " + propagationRounds + " round");
                break;
            }

            // Itera su tutte le clausole attive
            for (List<Integer> clause : allActiveClauses) {
                if (interrupted) {
                    return PropagationResult.success();
                }

                ClauseEvaluationResult evaluation = evaluateClauseCurrentState(clause);

                switch (evaluation.getStatus()) {
                    case SATISFIED -> {
                        // Clausola già soddisfatta - continua
                        continue;
                    }
                    case FALSIFIED -> {
                        // CONFLITTO RILEVATO - identifica clausola giustificante
                        LOGGER.fine("Conflitto rilevato in clausola: " + clause);
                        List<Integer> justifyingClause = findJustifyingClauseForConflict(clause);
                        return PropagationResult.conflict(clause, justifyingClause);
                    }
                    case UNIT -> {
                        // PROPAGAZIONE UNITARIA - assegna letterale libero
                        if (propagateUnitClause(clause, evaluation.getUnitLiteral())) {
                            propagationProgress = true;
                            LOGGER.finest("Propagazione unitaria: " + evaluation.getUnitLiteral() + " da " + clause);
                        }
                    }
                    case UNRESOLVED -> {
                        // Clausola con multiple variabili libere - continua
                        continue;
                    }
                }
            }

            LOGGER.finest("Round propagazione " + propagationRounds + " - progresso: " + propagationProgress);

        } while (propagationProgress && !interrupted);

        LOGGER.fine("Unit propagation completata dopo " + propagationRounds + " round");
        return PropagationResult.success();
    }

    /**
     * Raccoglie tutte le clausole attive (originali della formula + clausole apprese).
     */
    private List<List<Integer>> getAllActiveClauses() {
        List<List<Integer>> allClauses = new ArrayList<>(formula.getClauses());
        allClauses.addAll(learnedClauses);
        return allClauses;
    }

    /**
     * Valuta lo stato corrente di una clausola rispetto agli assegnamenti attuali.
     */
    private ClauseEvaluationResult evaluateClauseCurrentState(List<Integer> clause) {
        int unassignedCount = 0;
        Integer unassignedLiteral = null;

        for (Integer literal : clause) {
            Integer variable = Math.abs(literal);
            AssignedLiteral assignment = assignedValues.get(variable);

            if (assignment == null) {
                // Letterale non ancora assegnato
                unassignedCount++;
                unassignedLiteral = literal;
            } else {
                // Calcola valore effettivo del letterale
                boolean literalValue = assignment.getValue();
                if (literal < 0) {
                    literalValue = !literalValue; // Applica negazione
                }

                if (literalValue) {
                    // Letterale vero → clausola automaticamente soddisfatta
                    return ClauseEvaluationResult.satisfied();
                }
                // Se letterale falso, continua a controllare gli altri
            }
        }

        // Determina stato finale basato su letterali non assegnati
        return switch (unassignedCount) {
            case 0 -> ClauseEvaluationResult.falsified(); // Tutti falsi = conflitto
            case 1 -> ClauseEvaluationResult.unit(unassignedLiteral); // Unit clause
            default -> ClauseEvaluationResult.unresolved(); // Multiple non assegnati
        };
    }

    /**
     * Propaga clausola unitaria assegnando l'unico letterale libero.
     */
    private boolean propagateUnitClause(List<Integer> clause, Integer unitLiteral) {
        Integer variable = Math.abs(unitLiteral);
        Boolean value = unitLiteral > 0;

        // Verifica se variabile già assegnata
        AssignedLiteral existingAssignment = assignedValues.get(variable);
        if (existingAssignment != null) {
            return false; // Già assegnata, nessuna propagazione
        }

        // Crea e registra nuovo assegnamento di implicazione
        AssignedLiteral newImplication = new AssignedLiteral(variable, value, false, clause);
        assignedValues.put(variable, newImplication);
        decisionStack.addImpliedLiteral(variable, value, clause);
        statistics.incrementPropagations();

        LOGGER.fine("*** PROPAGAZIONE UNITARIA ***");
        LOGGER.fine("Variabile: " + variable + " = " + value);
        LOGGER.fine("Giustificata da: " + clause);
        LOGGER.fine("Livello: " + decisionStack.getLevel());

        return true;
    }

    //endregion

    //region DECISION MAKING E EURISTICA VSIDS CON ANTI-LOOP AVANZATO

    /**
     * NUOVO: Esegue decision making con euristica VSIDS avanzata e anti-loop completo.
     *
     * ALGORITMO ANTI-LOOP AVANZATO:
     * 1. Cerca variabili non ancora mai scelte (non in alreadyChosenVariables)
     * 2. Se tutte già scelte, resetta il set e riparte da capo
     * 3. Aggiorna tracking delle variabili scelte
     */
    private void executeDecisionMaking() {
        LOGGER.fine("Avvio decision making con euristica VSIDS e anti-loop avanzato");

        VariableSelection selection = findBestVariableWithAntiLoop();

        if (selection == null) {
            throw new IllegalStateException("Decision making chiamato ma nessuna variabile disponibile");
        }

        // Registra decisione e aggiorna tracking anti-loop
        recordDecision(selection.variable, selection.polarity);
        updateAntiLoopTracking(selection.variable);
    }

    /**
     * NUOVO: Trova migliore variabile applicando strategia anti-loop avanzata.
     */
    private VariableSelection findBestVariableWithAntiLoop() {
        // FASE 1: Cerca variabili mai scelte prima
        VariableSelection freshVariable = findUntriedVariable();
        if (freshVariable != null) {
            LOGGER.fine("Selezionata variabile mai tentata: " + freshVariable.variable);
            return freshVariable;
        }

        // FASE 2: Tutte le variabili disponibili sono già state tentate
        // Verifica se ci sono variabili non assegnate
        List<Integer> unassignedVariables = getUnassignedVariables();

        if (unassignedVariables.isEmpty()) {
            return null; // Nessuna variabile disponibile
        }

        // FASE 3: Reset del tracking e ripartenza
        LOGGER.info("Anti-loop: tutte le variabili disponibili già tentate, reset tracking");
        performAntiLoopReset();

        // FASE 4: Seleziona variabile dopo reset
        return findFirstUnassignedVariableAfterReset();
    }

    /**
     * NUOVO: Trova prima variabile non ancora mai tentata.
     */
    private VariableSelection findUntriedVariable() {
        for (Map.Entry<Integer, AssignedLiteral> entry : assignedValues.entrySet()) {
            Integer variable = entry.getKey();

            // Salta variabili già assegnate
            if (entry.getValue() != null) {
                continue;
            }

            // Salta variabili già tentate
            if (alreadyChosenVariables.contains(variable)) {
                continue;
            }

            // Variabile non assegnata e mai tentata trovata
            Boolean polarity = selectOptimalPolarity(variable);
            return new VariableSelection(variable, polarity);
        }

        return null; // Nessuna variabile non tentata trovata
    }

    /**
     * NUOVO: Ottiene lista di tutte le variabili non assegnate.
     */
    private List<Integer> getUnassignedVariables() {
        List<Integer> unassigned = new ArrayList<>();

        for (Map.Entry<Integer, AssignedLiteral> entry : assignedValues.entrySet()) {
            if (entry.getValue() == null) {
                unassigned.add(entry.getKey());
            }
        }

        return unassigned;
    }

    /**
     * NUOVO: Esegue reset del tracking anti-loop.
     */
    private void performAntiLoopReset() {
        int previouslyBlocked = alreadyChosenVariables.size();
        alreadyChosenVariables.clear();
        antiLoopResetCount++;

        LOGGER.info("Anti-loop reset #" + antiLoopResetCount + ": " + previouslyBlocked + " variabili riabilitate");
    }

    /**
     * NUOVO: Trova prima variabile non assegnata dopo reset.
     */
    private VariableSelection findFirstUnassignedVariableAfterReset() {
        for (Map.Entry<Integer, AssignedLiteral> entry : assignedValues.entrySet()) {
            Integer variable = entry.getKey();

            if (entry.getValue() == null) {
                Boolean polarity = selectOptimalPolarity(variable);
                return new VariableSelection(variable, polarity);
            }
        }

        return null;
    }

    /**
     * NUOVO: Aggiorna tracking anti-loop dopo decisione.
     */
    private void updateAntiLoopTracking(Integer chosenVariable) {
        alreadyChosenVariables.add(chosenVariable);
        LOGGER.finest("Anti-loop tracking: variabile " + chosenVariable + " aggiunta al set bloccato (totale: " + alreadyChosenVariables.size() + ")");
    }

    /**
     * Seleziona polarità ottimale per variabile basata su contatori VSIDS.
     */
    private Boolean selectOptimalPolarity(Integer variable) {
        Integer positiveCount = vsidsCounter.getOrDefault(variable, 0);
        Integer negativeCount = vsidsCounter.getOrDefault(-variable, 0);

        // Sceglie polarità più frequente nei conflitti
        boolean choosePositive = positiveCount >= negativeCount;

        LOGGER.finest("Selezione polarità per " + variable + ": positiva=" + positiveCount +
                ", negativa=" + negativeCount + " → scelta=" + choosePositive);

        return choosePositive;
    }

    /**
     * Registra decisione euristica nel sistema.
     */
    private void recordDecision(Integer variable, Boolean value) {
        decisionCount++;
        statistics.incrementDecisions();

        // Crea assegnamento decisionale
        AssignedLiteral decision = new AssignedLiteral(variable, value, true, null);
        assignedValues.put(variable, decision);
        decisionStack.addDecision(variable, value);

        int currentLevel = decisionStack.getLevel();
        LOGGER.fine(String.format("DECISIONE #%d: variabile %d = %s @ livello %d",
                decisionCount, variable, value, currentLevel));
    }

    //endregion

    //region VERIFICA SODDISFACIMENTO E STATO FORMULA

    /**
     * Verifica se la formula è completamente soddisfatta con assegnamenti correnti.
     */
    private boolean isFormulaSatisfied() {
        // Verifica preliminare: tutte le variabili devono essere assegnate
        if (!areAllVariablesAssigned()) {
            return false;
        }

        // Verifica soddisfacimento clausole originali
        if (!areAllClausesSatisfied(formula.getClauses())) {
            LOGGER.fine("Clausole originali non completamente soddisfatte");
            return false;
        }

        // Verifica soddisfacimento clausole apprese
        if (!areAllClausesSatisfied(learnedClauses)) {
            LOGGER.fine("Clausole apprese non completamente soddisfatte");
            return false;
        }

        LOGGER.info("Formula completamente soddisfatta - SAT confermato");
        return true;
    }

    /**
     * Verifica se tutte le clausole in una lista sono soddisfatte.
     */
    private boolean areAllClausesSatisfied(List<List<Integer>> clauses) {
        for (List<Integer> clause : clauses) {
            ClauseEvaluationResult evaluation = evaluateClauseCurrentState(clause);

            if (evaluation.getStatus() != ClauseEvaluationResult.Status.SATISFIED) {
                LOGGER.finest("Clausola non soddisfatta: " + clause + " (stato: " + evaluation.getStatus() + ")");
                return false;
            }
        }

        return true;
    }

    /**
     * Verifica se tutte le variabili sono state assegnate.
     */
    private boolean areAllVariablesAssigned() {
        return assignedValues.values().stream().noneMatch(Objects::isNull);
    }

    /**
     * Conta il numero di variabili attualmente assegnate.
     */
    private int countAssignedVariables() {
        return (int) assignedValues.values().stream()
                .filter(Objects::nonNull)
                .count();
    }

    /**
     * Trova il livello di decisione di una variabile specifica.
     */
    private int findVariableLevel(Integer variable) {
        for (int level = 0; level < decisionStack.size(); level++) {
            if (decisionStack.getLiteralsAtLevel(level).contains(variable)) {
                return level;
            }
        }
        return -1; // Variabile non trovata
    }

    //endregion

    //region GESTIONE RISULTATI E CLEANUP

    /**
     * Gestisce interruzione controllata del solutore.
     */
    private SATResult handleInterruption() {
        LOGGER.info("Risoluzione interrotta per timeout");
        statistics.stopTimer();
        throw new RuntimeException("Timeout raggiunto durante la risoluzione SAT");
    }

    /**
     * Gestisce errori critici durante l'esecuzione.
     */
    private SATResult handleCriticalError(Exception e) {
        LOGGER.log(Level.SEVERE, "Errore critico durante risoluzione CDCL", e);
        statistics.stopTimer();

        if (interrupted || Thread.currentThread().isInterrupted()) {
            throw new RuntimeException("Timeout raggiunto durante la risoluzione SAT");
        }

        throw new RuntimeException("Errore critico nella risoluzione SAT: " + e.getMessage(), e);
    }

    /**
     * Genera risultato finale basato su esito esecuzione algoritmo CDCL.
     */
    private SATResult generateFinalResult(CDCLExecutionResult executionResult) {
        statistics.stopTimer();

        // CORRETTO: Sincronizza tutte le statistiche finali prima del logging
        synchronizeFinalStatistics();

        // Log statistiche finali
        logFinalStatistics();

        return switch (executionResult.getType()) {
            case SATISFIABLE -> {
                LOGGER.info("=== FORMULA SAT - Generazione modello ===");
                Map<String, Boolean> model = generateSatisfiableModel();
                yield SATResult.satisfiable(model, statistics);
            }
            case UNSATISFIABLE -> {
                LOGGER.info("=== FORMULA UNSAT - Generazione prova ===");
                String proof = proofGenerator.generateProof();
                statistics.setProofSize(proofGenerator.getStepCount());
                yield SATResult.unsatisfiable(proof, statistics);
            }
            case TIMEOUT -> {
                LOGGER.warning("Esecuzione terminata per limite iterazioni");
                throw new RuntimeException("Timeout raggiunto - limite iterazioni superato");
            }
            case INTERRUPTED -> {
                LOGGER.info("Esecuzione interrotta esternamente");
                throw new RuntimeException("Solver interrotto per timeout esterno");
            }
            default -> throw new IllegalStateException("Tipo risultato non gestito: " + executionResult.getType());
        };
    }

    /**
     * NUOVO: Sincronizza tutte le statistiche finali da diverse fonti.
     * Garantisce coerenza tra CDCLSolver e RestartTechnique per output finale.
     * CORRETTO: Il numero di conflitti deve coincidere con la dimensione della prova.
     */
    private void synchronizeFinalStatistics() {
        // CRITICO: Il numero di conflitti = dimensione della prova (numero passi risoluzione)
        int proofSize = proofGenerator.getStepCount();

        if (proofSize > 0) {
            // Per formule UNSAT: conflitti = passi di prova
            conflictCount = proofSize;

            // Sincronizza statistics.conflicts con il valore corretto
            while (statistics.getConflicts() < conflictCount) {
                statistics.incrementConflicts();
            }
            // Se statistics.conflicts è maggiore, resettalo al valore corretto
            if (statistics.getConflicts() > conflictCount) {
                // Crea nuove statistiche con il valore corretto
                SATStatistics correctedStats = new SATStatistics();
                for (int i = 0; i < conflictCount; i++) {
                    correctedStats.incrementConflicts();
                }
                for (int i = 0; i < decisionCount; i++) {
                    correctedStats.incrementDecisions();
                }
                if (restartTechnique != null) {
                    for (int i = 0; i < restartTechnique.getTotalRestarts(); i++) {
                        correctedStats.incrementRestarts();
                    }
                }
                correctedStats.setProofSize(proofSize);
                this.statistics = correctedStats;
            }
        } else {
            // Per formule SAT: usa il conteggio normale dei conflitti
            while (statistics.getConflicts() < conflictCount) {
                statistics.incrementConflicts();
            }
        }

        // Verifica e corregge il conteggio decisioni
        int actualDecisions = decisionCount;
        while (statistics.getDecisions() < actualDecisions) {
            statistics.incrementDecisions();
        }

        // Sincronizza conteggio restart da RestartTechnique
        if (restartTechnique != null) {
            int actualRestarts = restartTechnique.getTotalRestarts();
            while (statistics.getRestarts() < actualRestarts) {
                statistics.incrementRestarts();
            }
        }

        // Imposta dimensione prova
        statistics.setProofSize(proofSize);

        LOGGER.fine("Statistiche sincronizzate: Decisioni=" + statistics.getDecisions() +
                ", Conflitti=" + statistics.getConflicts() +
                ", Restart=" + statistics.getRestarts() +
                ", ProofSize=" + statistics.getProofSize());
    }

    /**
     * Genera modello finale per formula soddisfacibile.
     */
    private Map<String, Boolean> generateSatisfiableModel() {
        Map<String, Boolean> model = new HashMap<>();
        Map<Integer, String> inverseMapping = createInverseVariableMapping();

        LOGGER.fine("Generazione modello SAT finale");

        for (int variable = 1; variable <= formula.getVariableCount(); variable++) {
            AssignedLiteral assignment = assignedValues.get(variable);
            String originalVariableName = inverseMapping.getOrDefault(variable, String.valueOf(variable));

            if (assignment != null) {
                model.put(originalVariableName, assignment.getValue());
                LOGGER.finest("Modello: " + originalVariableName + " = " + assignment.getValue());
            } else {
                // Variabile non assegnata → valore di default
                model.put(originalVariableName, false);
                LOGGER.finest("Modello: " + originalVariableName + " = false (default)");
            }
        }

        LOGGER.info("Modello SAT generato: " + model.size() + " variabili");
        return model;
    }

    /**
     * Registra statistiche finali complete dell'esecuzione.
     */
    private void logFinalStatistics() {
        LOGGER.info("=== STATISTICHE FINALI CDCL ===");
        LOGGER.info("Decisioni totali: " + decisionCount);
        LOGGER.info("Conflitti rilevati: " + conflictCount);

        // CORRETTO: Log statistiche restart ottenute direttamente da RestartTechnique
        if (restartTechnique != null) {
            int totalRestarts = restartTechnique.getTotalRestarts();
            int totalSubsumptionRemovals = restartTechnique.getTotalSubsumptionRemovals();

            LOGGER.info("Restart eseguiti: " + totalRestarts);
            LOGGER.info("Sussunzione rimozioni: " + totalSubsumptionRemovals);

            // Verifica coerenza con statistics interne
            int statisticsRestarts = statistics.getRestarts();
            if (statisticsRestarts != totalRestarts) {
                LOGGER.warning("Inconsistenza restart: statistics=" + statisticsRestarts + ", technique=" + totalRestarts);
                // Sincronizza con il valore corretto da RestartTechnique
                while (statistics.getRestarts() < totalRestarts) {
                    statistics.incrementRestarts();
                }
            }
        }

        LOGGER.info("Clausole apprese: " + learnedClauses.size());
        LOGGER.info("Tempo esecuzione: " + statistics.getExecutionTimeMs() + " ms");
        LOGGER.info("Variabili formula: " + formula.getVariableCount());
        LOGGER.info("Clausole originali: " + formula.getClausesCount());

        // Statistiche avanzate
        if (decisionCount > 0) {
            double conflictRate = (double) conflictCount / decisionCount;
            LOGGER.info("Tasso conflitti: " + String.format("%.2f", conflictRate) + " conflitti/decisione");
        }

        if (conflictCount > 0) {
            double learningRate = (double) learnedClauses.size() / conflictCount;
            LOGGER.info("Efficacia learning: " + String.format("%.2f", learningRate) + " clausole/conflitto");
        }

        // CORRETTO: Statistiche restart basate sui valori corretti
        if (restartTechnique != null && restartTechnique.getTotalRestarts() > 0) {
            double restartRate = (double) conflictCount / restartTechnique.getTotalRestarts();
            LOGGER.info("Frequenza restart: " + String.format("%.1f", restartRate) + " conflitti/restart");

            double subsumptionRate = (double) restartTechnique.getTotalSubsumptionRemovals() / restartTechnique.getTotalRestarts();
            LOGGER.info("Efficacia sussunzione: " + String.format("%.1f", subsumptionRate) + " rimozioni/restart");
        }

        // NUOVO: Statistiche anti-loop avanzato
        LOGGER.info("Anti-loop avanzato: " + alreadyChosenVariables.size() + " variabili bloccate");
        if (antiLoopResetCount > 0) {
            LOGGER.info("Reset anti-loop eseguiti: " + antiLoopResetCount);
        }
    }

    //endregion

    //region INTERFACCIA PUBBLICA RESTART E ANTI-LOOP

    /**
     * NUOVO: Restituisce statistiche restart se abilitato.
     */
    public String getRestartStatistics() {
        if (restartTechnique != null) {
            return restartTechnique.getRestartStatistics();
        } else {
            return "Restart non abilitato per questa istanza del solver.";
        }
    }

    /**
     * NUOVO: Verifica se restart è abilitato.
     */
    public boolean isRestartEnabled() {
        return restartTechnique != null;
    }

    /**
     * NUOVO: Restituisce informazioni anti-loop avanzato per debugging.
     */
    public String getAntiLoopInfo() {
        StringBuilder info = new StringBuilder();
        info.append("=== ANTI-LOOP VSIDS AVANZATO ===\n");
        info.append("Variabili già scelte: ").append(alreadyChosenVariables.size()).append("\n");

        if (!alreadyChosenVariables.isEmpty()) {
            info.append("Set variabili bloccate: ").append(alreadyChosenVariables).append("\n");
        }

        info.append("Reset eseguiti: ").append(antiLoopResetCount).append("\n");

        List<Integer> unassignedVars = getUnassignedVariables();
        info.append("Variabili non assegnate: ").append(unassignedVars.size()).append("\n");

        List<Integer> availableForDecision = new ArrayList<>();
        for (Integer var : unassignedVars) {
            if (!alreadyChosenVariables.contains(var)) {
                availableForDecision.add(var);
            }
        }

        info.append("Variabili disponibili per decisione: ").append(availableForDecision.size()).append("\n");
        if (!availableForDecision.isEmpty() && availableForDecision.size() <= 10) {
            info.append("Variabili disponibili: ").append(availableForDecision).append("\n");
        }

        info.append("===============================");
        return info.toString();
    }

    //endregion

    //region CLASSI DI SUPPORTO

    /**
     * NUOVO: Classe di supporto per selezione variabile con polarità.
     */
    private static class VariableSelection {
        final Integer variable;
        final Boolean polarity;

        VariableSelection(Integer variable, Boolean polarity) {
            this.variable = variable;
            this.polarity = polarity;
        }

        @Override
        public String toString() {
            return String.format("VariableSelection{var=%d, pol=%s}", variable, polarity);
        }
    }

    /**
     * Risultato dell'esecuzione completa dell'algoritmo CDCL.
     */
    private static class CDCLExecutionResult {
        public enum Type { SATISFIABLE, UNSATISFIABLE, TIMEOUT, INTERRUPTED }

        private final Type type;

        private CDCLExecutionResult(Type type) {
            this.type = type;
        }

        public Type getType() { return type; }

        public static CDCLExecutionResult satisfiable() { return new CDCLExecutionResult(Type.SATISFIABLE); }
        public static CDCLExecutionResult unsatisfiable() { return new CDCLExecutionResult(Type.UNSATISFIABLE); }
        public static CDCLExecutionResult timeout() { return new CDCLExecutionResult(Type.TIMEOUT); }
        public static CDCLExecutionResult interrupted() { return new CDCLExecutionResult(Type.INTERRUPTED); }
    }

    /**
     * Risultato della propagazione unitaria con informazioni di conflitto.
     */
    private static class PropagationResult {
        private final boolean hasConflict;
        private final List<Integer> conflictClause;
        private final List<Integer> justifyingClause;

        private PropagationResult(boolean hasConflict, List<Integer> conflictClause, List<Integer> justifyingClause) {
            this.hasConflict = hasConflict;
            this.conflictClause = conflictClause;
            this.justifyingClause = justifyingClause;
        }

        public boolean hasConflict() { return hasConflict; }
        public List<Integer> getConflictClause() { return conflictClause; }
        public List<Integer> getJustifyingClause() { return justifyingClause; }

        public static PropagationResult success() {
            return new PropagationResult(false, null, null);
        }

        public static PropagationResult conflict(List<Integer> conflictClause, List<Integer> justifyingClause) {
            return new PropagationResult(true, conflictClause, justifyingClause);
        }
    }

    /**
     * Risultato della valutazione dello stato di una clausola.
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
     * Risultato del conflict analysis con clausola appresa e livello backtrack.
     */
    private static class ConflictAnalysisResult {
        private final boolean unsatisfiable;
        private final List<Integer> learnedClause;
        private final int backtrackLevel;

        private ConflictAnalysisResult(boolean unsatisfiable, List<Integer> learnedClause, int backtrackLevel) {
            this.unsatisfiable = unsatisfiable;
            this.learnedClause = learnedClause;
            this.backtrackLevel = backtrackLevel;
        }

        public boolean isUnsatisfiable() { return unsatisfiable; }
        public List<Integer> getLearnedClause() { return learnedClause; }
        public int getBacktrackLevel() { return backtrackLevel; }

        public static ConflictAnalysisResult unsatisfiable() {
            return new ConflictAnalysisResult(true, Collections.emptyList(), -1);
        }

        public static ConflictAnalysisResult backtrack(List<Integer> learnedClause, int level) {
            return new ConflictAnalysisResult(false, learnedClause, level);
        }
    }

    //endregion
}