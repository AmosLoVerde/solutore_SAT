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
 * SOLUTORE CDCL AVANZATO - Implementazione completa con restart opzionale e anti-loop VSIDS
 *
 * Implementazione dell'algoritmo CDCL con integrazione opzionale della tecnica restart
 * per prevenzione stalli durante la ricerca SAT. Il restart è attivato solo quando
 * esplicitamente richiesto tramite configurazione.
 * 
 * Anti-loop VSIDS - Previene riselezionare immediatamente la stessa variabile
 * dopo backtrack per evitare loop infiniti nella ricerca.
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

    /** Tecnica restart opzionale (null se non abilitata) */
    private RestartTechnique restartTechnique;

    //endregion

    //region ANTI-LOOP VSIDS TRACKING

    /**
     * Ultima variabile scelta per decisione.
     * Utilizzata per prevenire riselezionare immediatamente la stessa variabile
     * dopo backtrack, evitando loop infiniti nella ricerca VSIDS.
     */
    private Integer lastChosenVariable;

    /**
     * Flag che indica se l'ultima decisione ha causato un backtrack.
     * Se true, la prossima decisione non può riselezionare lastChosenVariable.
     */
    private boolean lastDecisionCausedBacktrack;

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

        // Inizializzazione restart opzionale
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

        // Inizializzazione anti-loop VSIDS
        this.lastChosenVariable = null;
        this.lastDecisionCausedBacktrack = false;

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

        LOGGER.info("Anti-loop VSIDS: ATTIVO per prevenzione cicli infiniti");
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

        // Copia contatori correnti
        for (int i = 0; i < decisionCount; i++) {
            partialStats.incrementDecisions();
        }
        for (int i = 0; i < conflictCount; i++) {
            partialStats.incrementConflicts();
        }

        // Statistiche restart se abilitato
        if (restartTechnique != null) {
            for (int i = 0; i < restartTechnique.getTotalRestarts(); i++) {
                partialStats.incrementRestarts();
            }
        }

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

        // FASE INIZIALIZZAZIONE: Configura livello 0 con clausole unitarie
        initializeLevel0WithUnitClauses();

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
                // STEP 3: Conflict analysis con gestione restart integrata
                ConflictAnalysisResult analysisResult = executeConflictAnalysis(
                        propagationResult.getConflictClause(),
                        propagationResult.getJustifyingClause()
                );

                if (analysisResult.isUnsatisfiable()) {
                    LOGGER.info("Formula UNSAT determinata tramite conflict analysis");
                    return CDCLExecutionResult.unsatisfiable();
                }

                // STEP 4: Learning e backtracking
                executeLearningAndBacktrack(analysisResult);

                // Marca che l'ultima decisione ha causato backtrack
                markLastDecisionCausedBacktrack();

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

    /**
     * Marca che l'ultima decisione ha causato un backtrack.
     * Questo triggera l'anti-loop nella prossima selezione variabile.
     */
    private void markLastDecisionCausedBacktrack() {
        if (lastChosenVariable != null) {
            lastDecisionCausedBacktrack = true;
            LOGGER.finest("Anti-loop VSIDS attivato per variabile: " + lastChosenVariable);
        }
    }

    /**
     * Inizializza livello 0 con tutte le clausole unitarie originali della formula.
     */
    private void initializeLevel0WithUnitClauses() {
        LOGGER.fine("=== INIZIALIZZAZIONE LIVELLO 0 CON CLAUSOLE UNITARIE ===");

        List<List<Integer>> allClauses = formula.getClauses();
        int unitClausesAdded = 0;

        for (List<Integer> clause : allClauses) {
            if (clause.size() == 1) {
                Integer literal = clause.get(0);
                Integer variable = Math.abs(literal);
                Boolean value = literal > 0;

                // Verifica se variabile già assegnata
                if (assignedValues.get(variable) == null) {
                    // Aggiunge assegnamento unitario al livello 0
                    AssignedLiteral unitAssignment = new AssignedLiteral(variable, value, false, clause);
                    assignedValues.put(variable, unitAssignment);
                    decisionStack.addImpliedLiteral(variable, value, clause);

                    // Registra mapping per uso nelle spiegazioni
                    unitClauseMapping.put(literal, new ArrayList<>(clause));
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
        if (lastDecisionCausedBacktrack && lastChosenVariable != null) {
            antiLoopInfo = String.format(", Anti-loop attivo (var %d bloccata)", lastChosenVariable);
        }

        LOGGER.fine(String.format("Iterazione %d - Livello: %d, Decisioni: %d, Conflitti: %d%s, Assegnate: %d/%d%s",
                iterationCount, currentLevel, decisionCount, conflictCount, restartInfo, assignedCount, totalVariables, antiLoopInfo));
    }

    //endregion

    //region CONFLICT ANALYSIS CON RESTART INTEGRATO

    /**
     * Esegue conflict analysis completo con gestione restart opzionale.
     */
    private ConflictAnalysisResult executeConflictAnalysis(List<Integer> conflictClause,
                                                           List<Integer> justifyingClause) {
        LOGGER.fine("=== CONFLICT ANALYSIS AVANZATO ===");
        LOGGER.fine("Clausola conflitto: " + conflictClause);
        LOGGER.fine("Clausola giustificante: " + justifyingClause);

        // Aggiorna statistiche
        conflictCount++;
        statistics.incrementConflicts();

        // Aggiorna contatori VSIDS per migliorare euristica futura
        updateVSIDSCountersAfterConflict(conflictClause);

        // Gestione restart se abilitato
        if (restartTechnique != null) {
            boolean shouldRestart = restartTechnique.registerConflictAndCheckRestart();

            if (shouldRestart) {
                // Esegue conflict analysis normale prima del restart
                ConflictAnalysisResult normalResult = performNormalConflictAnalysis(conflictClause, justifyingClause);

                // Se UNSAT, non esegue restart
                if (normalResult.isUnsatisfiable()) {
                    LOGGER.info("Formula UNSAT determinata - restart non necessario");
                    return normalResult;
                }

                // Esegue restart e ritorna risultato speciale
                return executeRestartProcedure(normalResult);
            }
        }

        // Conflict analysis normale senza restart
        return performNormalConflictAnalysis(conflictClause, justifyingClause);
    }

    /**
     * Esegue conflict analysis normale (esistente).
     */
    private ConflictAnalysisResult performNormalConflictAnalysis(List<Integer> conflictClause,
                                                                 List<Integer> justifyingClause) {
        // Determina tipo di conflitto e strategia di analisi
        if (justifyingClause != null) {
            return analyzeNormalConflictWithExplanation(conflictClause, justifyingClause);
        } else {
            return analyzeDirectConflict(conflictClause);
        }
    }

    /**
     * Esegue procedura restart completa.
     */
    private ConflictAnalysisResult executeRestartProcedure(ConflictAnalysisResult normalResult) {
        LOGGER.info("=== ESECUZIONE RESTART PROCEDURA ===");

        try {
            // Prepara dati per restart
            List<AssignedLiteral> level0Assignments = decisionStack.getAssignmentsAtLevel(0);
            List<List<Integer>> currentLearnedClauses = new ArrayList<>(learnedClauses);

            // Apprendi clausola dal conflict analysis normale
            if (normalResult.getLearnedClause() != null && !normalResult.getLearnedClause().isEmpty()) {
                learnClauseIfNovel(normalResult.getLearnedClause());
                currentLearnedClauses.add(normalResult.getLearnedClause());
            }

            // Esegue restart
            RestartTechnique.RestartResult restartResult = restartTechnique.executeRestart(
                    level0Assignments, currentLearnedClauses);

            // Aggiorna statistiche
            statistics.incrementRestarts();

            // Esegue backtrack al livello 0
            performRestartBacktrack();

            // Aggiorna clausole apprese con quelle ottimizzate
            updateLearnedClausesFromRestart(restartResult);

            // Reset anti-loop dopo restart
            resetAntiLoopTracking();

            LOGGER.info("Restart #" + restartResult.restartNumber + " completato");
            LOGGER.info("Sussunzione: " + restartResult.subsumptionRemovals + " clausole rimosse");

            // Ritorna segnale di continuazione normale
            return ConflictAnalysisResult.backtrack(Collections.emptyList(), 0);

        } catch (Exception e) {
            LOGGER.log(Level.WARNING, "Errore durante restart", e);
            // Fallback: continua con backtrack normale
            return normalResult;
        }
    }

    /**
     * Reset del tracking anti-loop dopo restart.
     * Il restart resetta completamente la ricerca quindi è sicuro ripartire da capo.
     */
    private void resetAntiLoopTracking() {
        lastChosenVariable = null;
        lastDecisionCausedBacktrack = false;
        LOGGER.fine("Anti-loop VSIDS: Reset dopo restart");
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

    //region CONFLICT ANALYSIS METODI ESISTENTI

    /**
     * Analizza conflitto normale generando spiegazione tra clausola giustificante e conflitto.
     */
    private ConflictAnalysisResult analyzeNormalConflictWithExplanation(List<Integer> conflictClause,
                                                                        List<Integer> justifyingClause) {
        LOGGER.info("Analisi conflitto normale con spiegazione matematica");

        // Genera spiegazione tra le due clausole
        List<Integer> explanation = generateMathematicalExplanation(justifyingClause, conflictClause);

        LOGGER.info("Spiegazione generata: " + justifyingClause + " ∧ " + conflictClause + " ⊢ " + explanation);

        // Registra passo di spiegazione per prova
        proofGenerator.recordResolutionStep(justifyingClause, conflictClause, explanation);

        // Verifica se derivata clausola vuota (UNSAT)
        if (explanation.isEmpty()) {
            LOGGER.info("*** CLAUSOLA VUOTA DERIVATA - FORMULA UNSAT ***");
            return ConflictAnalysisResult.unsatisfiable();
        }

        // Processa risultato spiegazione
        return processExplanationResult(explanation);
    }

    /**
     * Analizza conflitto diretto su clausola completamente falsificata.
     */
    private ConflictAnalysisResult analyzeDirectConflict(List<Integer> conflictClause) {
        LOGGER.info("Analisi conflitto diretto su clausola falsificata");

        // Verifica se tutti letterali sono al livello 0
        if (areAllLiteralsAtLevel0(conflictClause)) {
            LOGGER.info("Conflitto diretto al livello 0 - avvio spiegazioni sequenziali");
            return executeSequentialExplanationsForLevel0(conflictClause);
        }

        // Conflitto a livelli superiori
        LOGGER.info("Conflitto diretto a livelli superiori - formula UNSAT");
        return ConflictAnalysisResult.unsatisfiable();
    }

    /**
     * Processa il risultato di una spiegazione determinando azione appropriata.
     */
    private ConflictAnalysisResult processExplanationResult(List<Integer> explanation) {
        // CASO 1: Spiegazione unitaria
        if (explanation.size() == 1) {
            return processUnitaryExplanation(explanation.get(0));
        }

        // CASO 2: Verifica conflitto totale con livello 0
        if (areAllLiteralsInConflictWithLevel0(explanation)) {
            return executeSequentialExplanationsForLevel0(explanation);
        }

        // CASO 3: Spiegazione normale - calcola livello backtrack
        int backtrackLevel = calculateOptimalBacktrackLevel(explanation);
        return ConflictAnalysisResult.backtrack(explanation, backtrackLevel);
    }

    /**
     * Processa spiegazione unitaria verificando conflitti con livello 0.
     */
    private ConflictAnalysisResult processUnitaryExplanation(Integer unitLiteral) {
        Integer variable = Math.abs(unitLiteral);
        Boolean expectedValue = unitLiteral > 0;

        // Verifica conflitto con assegnamento livello 0
        AssignedLiteral existingAssignment = assignedValues.get(variable);
        if (existingAssignment != null && findVariableLevel(variable) == 0) {
            if (!existingAssignment.getValue().equals(expectedValue)) {
                // Conflitto con livello 0 → genera clausola vuota
                List<Integer> contradictoryUnit = Arrays.asList(-unitLiteral);
                List<Integer> emptyClause = Collections.emptyList();
                proofGenerator.recordResolutionStep(Arrays.asList(unitLiteral), contradictoryUnit, emptyClause);

                LOGGER.info("Conflitto unitario con livello 0 - UNSAT derivato");
                return ConflictAnalysisResult.unsatisfiable();
            }
        }

        // Nessun conflitto - backtrack al livello 0
        return ConflictAnalysisResult.backtrack(Arrays.asList(unitLiteral), 0);
    }

    /**
     * Esegue spiegazioni sequenziali per risoluzione conflitti al livello 0.
     */
    private ConflictAnalysisResult executeSequentialExplanationsForLevel0(List<Integer> initialClause) {
        LOGGER.info("=== SPIEGAZIONI SEQUENZIALI LIVELLO 0 ===");
        LOGGER.info("Clausola iniziale: " + initialClause);

        List<Integer> currentClause = new ArrayList<>(initialClause);
        int explanationSteps = 0;
        final int MAX_EXPLANATION_STEPS = 100;

        while (!currentClause.isEmpty() && explanationSteps < MAX_EXPLANATION_STEPS) {
            explanationSteps++;

            // Trova prossimo letterale da consumare
            Integer literalToConsume = findNextLiteralToConsume(currentClause);
            if (literalToConsume == null) {
                LOGGER.warning("Impossibile trovare letterale da consumare in: " + currentClause);
                break;
            }

            // Trova clausola unitaria corrispondente
            List<Integer> unitClause = findUnitClauseForLiteral(literalToConsume);
            if (unitClause == null) {
                LOGGER.warning("Clausola unitaria non trovata per letterale: " + literalToConsume);
                break;
            }

            // Genera prossima spiegazione
            List<Integer> nextClause = generateMathematicalExplanation(currentClause, unitClause);

            LOGGER.info("Spiegazione sequenziale " + explanationSteps + ": " + currentClause + " ∧ " + unitClause + " ⊢ " + nextClause);

            // Registra passo per prova
            proofGenerator.recordResolutionStep(currentClause, unitClause, nextClause);

            // Aggiorna clausola corrente
            currentClause = nextClause;

            // Verifica clausola vuota
            if (currentClause.isEmpty()) {
                LOGGER.info("*** CLAUSOLA VUOTA DERIVATA DA SPIEGAZIONI SEQUENZIALI (Step " + explanationSteps + ") ***");
                return ConflictAnalysisResult.unsatisfiable();
            }
        }

        if (explanationSteps >= MAX_EXPLANATION_STEPS) {
            LOGGER.warning("Spiegazioni sequenziali interrotte per limite step: " + MAX_EXPLANATION_STEPS);
        }

        LOGGER.warning("Spiegazioni sequenziali terminate senza clausola vuota. Clausola finale: " + currentClause);
        return ConflictAnalysisResult.unsatisfiable();
    }

    /**
     * Trova il prossimo letterale da consumare nelle spiegazioni sequenziali.
     */
    private Integer findNextLiteralToConsume(List<Integer> clause) {
        for (Integer literal : clause) {
            Integer variable = Math.abs(literal);
            AssignedLiteral assignment = assignedValues.get(variable);

            if (assignment != null && findVariableLevel(variable) == 0) {
                Boolean expectedValue = literal > 0;
                if (!assignment.getValue().equals(expectedValue)) {
                    // Letterale in conflitto → restituisce opposto per clausola unitaria
                    return -literal;
                }
            }
        }
        return null;
    }

    /**
     * Trova clausola unitaria che contiene il letterale specificato.
     */
    private List<Integer> findUnitClauseForLiteral(Integer literal) {
        // Cerca nel mapping clausole unitarie originali
        List<Integer> mappedClause = unitClauseMapping.get(literal);
        if (mappedClause != null) {
            return mappedClause;
        }

        // Genera clausola unitaria sintetica se necessario
        Integer variable = Math.abs(literal);
        AssignedLiteral assignment = assignedValues.get(variable);

        if (assignment != null && findVariableLevel(variable) == 0) {
            return Arrays.asList(literal);
        }

        return null;
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
     * Verifica se tutti i letterali di una clausola sono assegnati al livello 0.
     */
    private boolean areAllLiteralsAtLevel0(List<Integer> clause) {
        for (Integer literal : clause) {
            Integer variable = Math.abs(literal);
            if (findVariableLevel(variable) != 0) {
                return false;
            }
        }
        return true;
    }

    /**
     * Verifica se tutti i letterali sono in conflitto con assegnamenti livello 0.
     */
    private boolean areAllLiteralsInConflictWithLevel0(List<Integer> clause) {
        for (Integer literal : clause) {
            Integer variable = Math.abs(literal);
            AssignedLiteral assignment = assignedValues.get(variable);

            if (assignment == null || findVariableLevel(variable) != 0) {
                return false;
            }

            Boolean expectedValue = literal > 0;
            if (assignment.getValue().equals(expectedValue)) {
                return false; // Non in conflitto
            }
        }
        return true;
    }

    /**
     * Calcola livello ottimale per backtracking basato su clausola appresa.
     */
    private int calculateOptimalBacktrackLevel(List<Integer> learnedClause) {
        if (learnedClause.size() == 1) {
            // Clausola unitaria → backtrack al livello 0 per auto-giustificazione
            return 0;
        } else {
            // Clausola multipla → trova livello dove diventa assertiva
            return findAssertionLevel(learnedClause);
        }
    }

    /**
     * Trova livello appropriato dove clausola appresa diventa assertiva.
     */
    private int findAssertionLevel(List<Integer> learnedClause) {
        int currentLevel = decisionStack.getLevel();
        // Strategia semplificata: backtrack di un livello per permettere assertion
        return Math.max(0, currentLevel - 1);
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

        LOGGER.fine("Propagazione unitaria eseguita: " + variable + " = " + value + " derivata da " + clause);
        return true;
    }

    /**
     * Identifica la clausola che ha giustificato l'ultima propagazione coinvolta nel conflitto.
     */
    private List<Integer> findJustifyingClauseForConflict(List<Integer> conflictClause) {
        AssignedLiteral mostRecentPropagation = null;
        int highestLevel = -1;

        // Trova l'implicazione più recente tra i letterali del conflitto
        for (Integer literal : conflictClause) {
            Integer variable = Math.abs(literal);
            AssignedLiteral assignment = assignedValues.get(variable);

            if (assignment != null && assignment.isImplication()) {
                int assignmentLevel = findVariableLevel(variable);
                if (assignmentLevel >= highestLevel) {
                    highestLevel = assignmentLevel;
                    mostRecentPropagation = assignment;
                }
            }
        }

        return mostRecentPropagation != null ? mostRecentPropagation.getAncestorClause() : null;
    }

    //endregion

    //region DECISION MAKING E EURISTICA VSIDS CON ANTI-LOOP

    /**
     * Esegue decision making con euristica VSIDS avanzata e anti-loop.
     *
     * ALGORITMO ANTI-LOOP:
     * 1. Se lastDecisionCausedBacktrack è true, salta lastChosenVariable
     * 2. Trova prossima variabile non assegnata nell'ordine di frequenza
     * 3. Se non trova alternative, riabilita lastChosenVariable come fallback
     * 4. Aggiorna tracking per prossima iterazione
     */
    private void executeDecisionMaking() {
        LOGGER.fine("Avvio decision making con euristica VSIDS e anti-loop");

        Integer selectedVariable = null;
        Boolean selectedPolarity = null;

        // Strategia di selezione con anti-loop
        if (lastDecisionCausedBacktrack && lastChosenVariable != null) {
            LOGGER.fine("Anti-loop attivo: evitando variabile " + lastChosenVariable);

            // Trova variabile alternativa escludendo quella bloccata
            VariableSelection selection = findAlternativeVariableWithAntiLoop(lastChosenVariable);

            if (selection != null) {
                selectedVariable = selection.variable;
                selectedPolarity = selection.polarity;
                LOGGER.fine("Variabile alternativa selezionata: " + selectedVariable + " (anti-loop)");
            } else {
                // Fallback: nessuna alternativa, riabilita la variabile bloccata
                LOGGER.fine("Nessuna alternativa trovata, riabilitando variabile " + lastChosenVariable);
                selectedVariable = lastChosenVariable;
                selectedPolarity = selectOptimalPolarity(lastChosenVariable);
            }

            // Reset flag anti-loop dopo una decisione
            lastDecisionCausedBacktrack = false;

        } else {
            // Strategia normale: prima variabile non assegnata
            VariableSelection selection = findFirstUnassignedVariable();
            if (selection != null) {
                selectedVariable = selection.variable;
                selectedPolarity = selection.polarity;
            }
        }

        // Validazione selezione
        if (selectedVariable == null) {
            throw new IllegalStateException("Decision making chiamato ma nessuna variabile disponibile");
        }

        // Registra decisione e aggiorna tracking
        recordDecision(selectedVariable, selectedPolarity);
        updateAntiLoopTracking(selectedVariable);
    }

    /**
     * Trova variabile alternativa escludendo quella bloccata dall'anti-loop.
     */
    private VariableSelection findAlternativeVariableWithAntiLoop(Integer blockedVariable) {
        for (Map.Entry<Integer, AssignedLiteral> entry : assignedValues.entrySet()) {
            Integer variable = entry.getKey();

            // Salta variabile bloccata e variabili già assegnate
            if (variable.equals(blockedVariable) || entry.getValue() != null) {
                continue;
            }

            // Variabile non assegnata e non bloccata trovata
            Boolean polarity = selectOptimalPolarity(variable);
            return new VariableSelection(variable, polarity);
        }

        return null; // Nessuna alternativa trovata
    }

    /**
     * Trova prima variabile non assegnata (strategia normale).
     */
    private VariableSelection findFirstUnassignedVariable() {
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
     * Aggiorna tracking anti-loop dopo decisione.
     */
    private void updateAntiLoopTracking(Integer chosenVariable) {
        lastChosenVariable = chosenVariable;
        // lastDecisionCausedBacktrack viene impostato a true solo se si verifica backtrack
        LOGGER.finest("Anti-loop tracking: lastChosenVariable = " + chosenVariable);
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

        // Log statistiche restart se abilitato
        if (restartTechnique != null) {
            LOGGER.info("Restart eseguiti: " + restartTechnique.getTotalRestarts());
            LOGGER.info("Sussunzione rimozioni: " + restartTechnique.getTotalSubsumptionRemovals());
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

        // Statistiche restart se disponibili
        if (restartTechnique != null && restartTechnique.getTotalRestarts() > 0) {
            double restartRate = (double) conflictCount / restartTechnique.getTotalRestarts();
            LOGGER.info("Frequenza restart: " + String.format("%.1f", restartRate) + " conflitti/restart");

            double subsumptionRate = (double) restartTechnique.getTotalSubsumptionRemovals() / restartTechnique.getTotalRestarts();
            LOGGER.info("Efficacia sussunzione: " + String.format("%.1f", subsumptionRate) + " rimozioni/restart");
        }

        // Statistiche anti-loop
        if (lastChosenVariable != null) {
            LOGGER.info("Ultima variabile scelta: " + lastChosenVariable);
            if (lastDecisionCausedBacktrack) {
                LOGGER.info("Anti-loop: variabile bloccata per prossima decisione");
            }
        }
    }

    //endregion

    //region INTERFACCIA PUBBLICA RESTART

    /**
     * Restituisce statistiche restart se abilitato.
     */
    public String getRestartStatistics() {
        if (restartTechnique != null) {
            return restartTechnique.getRestartStatistics();
        } else {
            return "Restart non abilitato per questa istanza del solver.";
        }
    }

    /**
     * Verifica se restart è abilitato.
     */
    public boolean isRestartEnabled() {
        return restartTechnique != null;
    }

    /**
     * Restituisce informazioni anti-loop per debugging.
     */
    public String getAntiLoopInfo() {
        StringBuilder info = new StringBuilder();
        info.append("=== ANTI-LOOP VSIDS INFO ===\n");
        info.append("Ultima variabile scelta: ").append(lastChosenVariable != null ? lastChosenVariable : "nessuna").append("\n");
        info.append("Backtrack flag attivo: ").append(lastDecisionCausedBacktrack).append("\n");

        if (lastDecisionCausedBacktrack && lastChosenVariable != null) {
            info.append("Variabile bloccata per prossima decisione: ").append(lastChosenVariable).append("\n");
        } else {
            info.append("Nessuna variabile bloccata\n");
        }

        info.append("============================");
        return info.toString();
    }

    //endregion

    //region CLASSI DI SUPPORTO

    /**
     * Classe di supporto per selezione variabile con polarità.
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