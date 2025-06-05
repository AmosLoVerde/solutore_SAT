package org.sat.cdcl;

import org.sat.cnf.CNFConverter;
import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;

/**
 * SOLUTORE CDCL (Conflict-Driven Clause Learning) per problemi SAT
 *
 * ALGORITMI IMPLEMENTATI:
 * - Unit Propagation: propaga clausole unitarie automaticamente
 * - VSIDS Heuristic: Variable State Independent Decaying Sum per selezione variabili
 * - Conflict Analysis con "spiegazione" matematicamente corretta
 * - Non-chronological backtracking: backjump intelligente ai livelli necessari
 * - Clause learning: apprende clausole dalle spiegazioni
 * - Complete proof generation: genera prove tramite spiegazioni sequenziali
 */
public class CDCLSolver {

    private static final Logger LOGGER = Logger.getLogger(CDCLSolver.class.getName());

    //region STRUTTURE DATI PRINCIPALI

    /** Formula CNF in rappresentazione ottimizzata per CDCL */
    private final CNFFormula formula;

    /** Stack gerarchico per gestione livelli di decisione e backtracking */
    private final DecisionStack decisionStack;

    /** Mappa variabile → assegnamento corrente (null = non assegnata) */
    private final Map<Integer, AssignedLiteral> assignedValues;

    /** Contatori VSIDS per euristica selezione variabili */
    private final Map<Integer, Integer> vsidsCounter;

    /** Clausole apprese durante conflict analysis */
    private final List<List<Integer>> learnedClauses;

    /** Generatore prove per formule UNSAT */
    private final ProofGenerator proofGenerator;

    //endregion

    //region STATO E STATISTICHE

    /** Statistiche di esecuzione (decisioni, conflitti, tempo) */
    private SATStatistics statistics;

    /** Contatore conflitti rilevati */
    private int conflictCount;

    /** Contatore decisioni prese */
    private int decisionCount;

    /** Flag interruzione esterna (timeout) */
    private volatile boolean interrupted = false;

    //endregion

    //region INIZIALIZZAZIONE E COSTRUZIONE

    /**
     * Costruisce il solutore CDCL con formula CNF.
     * Inizializza tutte le strutture dati e configura il generatore di prove.
     */
    public CDCLSolver(CNFConverter cnfConverter) {
        LOGGER.info("=== INIZIALIZZAZIONE SOLUTORE CDCL ===");

        // Inizializzazione strutture dati principali
        this.formula = new CNFFormula(cnfConverter);
        this.decisionStack = new DecisionStack();
        this.assignedValues = initializeVariableAssignments();
        this.vsidsCounter = initializeVSIDSCounters();
        this.learnedClauses = new ArrayList<>();

        // Configurazione generatore prove
        this.proofGenerator = new ProofGenerator();
        Map<Integer, String> inverseMapping = createInverseVariableMapping();
        proofGenerator.setVariableMapping(inverseMapping);

        // Inizializzazione contatori
        this.conflictCount = 0;
        this.decisionCount = 0;
        this.interrupted = false;

        // Log informazioni formula
        logFormulaInformation();
        LOGGER.info("=== SOLUTORE INIZIALIZZATO ===");
    }

    /**
     * Inizializza gli assegnamenti delle variabili ordinati per frequenza.
     */
    private LinkedHashMap<Integer, AssignedLiteral> initializeVariableAssignments() {
        // Calcola frequenza di ogni variabile nelle clausole
        Map<Integer, Integer> frequencies = new HashMap<>();
        for (int var = 1; var <= formula.getVariableCount(); var++) {
            frequencies.put(var, 0);
        }

        for (List<Integer> clause : formula.getClauses()) {
            for (Integer literal : clause) {
                int variable = Math.abs(literal);
                frequencies.merge(variable, 1, Integer::sum);
            }
        }

        // Ordina variabili per frequenza (più frequenti prime)
        List<Map.Entry<Integer, Integer>> sortedByFrequency = new ArrayList<>(frequencies.entrySet());
        sortedByFrequency.sort(Map.Entry.<Integer, Integer>comparingByValue().reversed());

        // Crea mappa ordinata con assegnamenti null (non assegnate)
        LinkedHashMap<Integer, AssignedLiteral> orderedAssignments = new LinkedHashMap<>();
        for (Map.Entry<Integer, Integer> entry : sortedByFrequency) {
            orderedAssignments.put(entry.getKey(), null);
        }

        return orderedAssignments;
    }

    /**
     * Inizializza contatori VSIDS per ogni letterale (positivo e negativo).
     */
    private Map<Integer, Integer> initializeVSIDSCounters() {
        Map<Integer, Integer> counters = new HashMap<>();

        for (Integer variable : assignedValues.keySet()) {
            counters.put(variable, 0);     // Letterale positivo
            counters.put(-variable, 0);    // Letterale negativo
        }

        return counters;
    }

    /**
     * Crea mapping inverso: ID numerico → nome variabile originale
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
     * Registra informazioni sulla formula per debugging
     */
    private void logFormulaInformation() {
        int clauseCount = formula.getClausesCount();
        int variableCount = formula.getVariableCount();
        double ratio = variableCount > 0 ? (double) clauseCount / variableCount : 0;

        LOGGER.info(String.format("Formula caricata: %d clausole, %d variabili (ratio: %.2f)",
                clauseCount, variableCount, ratio));
    }

    //endregion

    //region INTERFACCIA PUBBLICA PRINCIPALE

    /**
     * METODO PRINCIPALE: risolve la formula CNF utilizzando l'algoritmo CDCL.
     */
    public SATResult solve() {
        LOGGER.info("=== INIZIO RISOLUZIONE CDCL ===");

        this.statistics = new SATStatistics();

        try {
            // Esecuzione loop principale CDCL
            CDCLLoopResult loopResult = executeCDCLMainLoop();

            // Gestione risultato finale
            return handleFinalResult(loopResult);

        } catch (InterruptedException e) {
            LOGGER.info("Risoluzione interrotta per timeout");
            statistics.stopTimer();
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
     * Interrompe la risoluzione (chiamato da thread esterno per timeout)
     */
    public void interrupt() {
        this.interrupted = true;
        LOGGER.info("Richiesta interruzione ricevuta");
    }

    /**
     * Restituisce statistiche parziali durante l'esecuzione (per timeout)
     */
    public SATStatistics getPartialStatistics() {
        SATStatistics partialStats = new SATStatistics();

        for (int i = 0; i < decisionCount; i++) {
            partialStats.incrementDecisions();
        }

        for (int i = 0; i < conflictCount; i++) {
            partialStats.incrementConflicts();
        }

        partialStats.setProofSize(proofGenerator.getStepCount());
        return partialStats;
    }

    //endregion

    //region LOOP PRINCIPALE CDCL CORRETTO

    /**
     * LOOP PRINCIPALE CDCL CORRETTO secondo la specifica fornita
     */
    private CDCLLoopResult executeCDCLMainLoop() throws InterruptedException {
        LOGGER.fine("=== INIZIO LOOP PRINCIPALE CDCL CORRETTO ===");

        int iterationCount = 0;
        final int MAX_ITERATIONS = 10_000_000;

        // TODO: Bisogna aggiungere al livello 0 i letterali singoli
        List<List<Integer>> allClauses = getAllActiveClauses();
        for (List<Integer> clause : allClauses) {
            if (clause.size() == 1) {
                Integer literal = clause.getFirst();
                Integer variable = Math.abs(literal);
                Boolean value = literal > 0;

                // Verifica se già assegnata
                if (assignedValues.get(variable) == null) {
                    // Crea assegnamento al livello 0 (senza incrementare decisioni)
                    AssignedLiteral unitAssignment = new AssignedLiteral(variable, value, false, clause);
                    assignedValues.put(variable, unitAssignment);
                    decisionStack.addImpliedLiteral(variable, value, clause);

                    LOGGER.fine("Letterale unitario aggiunto al livello 0: " + variable + " = " + value + " da " + clause);
                }
            }
        }


        while (!interrupted) {
            iterationCount++;

            if (iterationCount > MAX_ITERATIONS) {
                LOGGER.warning("Raggiunto limite massimo iterazioni: " + MAX_ITERATIONS);
                return CDCLLoopResult.timeout();
            }

            checkForInterruption();

            LOGGER.finest("=== ITERAZIONE " + iterationCount + " ===");

            // FASE 1: VERIFICA SODDISFACIMENTO PRIMA DI TUTTO
            if (problemIsSatisfied()) {
                LOGGER.info("Formula SAT - tutte le clausole soddisfatte");
                return CDCLLoopResult.sat();
            }

            // FASE 2: UNIT PROPAGATION
            LOGGER.finest("Unit propagation - iterazione " + iterationCount);
            PropagationResult propagationResult = performUnitPropagation();

            if (propagationResult.hasConflict()) {
                // FASE 3: CONFLICT ANALYSIS CON SPIEGAZIONE
                LOGGER.fine("Conflitto rilevato - clausola: " + propagationResult.getConflictClause());

                ConflictAnalysisResult analysisResult = performConflictAnalysis(
                        propagationResult.getConflictClause(),
                        propagationResult.getJustifyingClause()
                );

                if (analysisResult.isUnsatisfiable()) {
                    LOGGER.info("Formula UNSAT determinata");
                    return CDCLLoopResult.unsat();
                }

                // FASE 4: APPRENDIMENTO E BACKTRACKING
                performLearningAndBacktrack(analysisResult);

                // Il nuovo apprendimento potrebbe causare propagazioni
                performUnitPropagation();
                continue;
            }


            // FASE 5: DECISIONE VSIDS se non ci sono conflitti e non siamo SAT
            if (!areAllVariablesAssigned()) {
                LOGGER.finest("Presa decisione - iterazione " + iterationCount);
                makeNextDecision();
            }

            // Log periodico progresso
            if (iterationCount % 1000 == 0) {
                logProgress(iterationCount);
            }
        }

        LOGGER.info("Loop CDCL terminato - Decisioni: " + decisionCount + ", Conflitti: " + conflictCount);
        return interrupted ? CDCLLoopResult.interrupted() : CDCLLoopResult.sat();
    }

    /**
     * Controlla se il thread corrente è stato interrotto
     */
    private void checkForInterruption() throws InterruptedException {
        if (Thread.currentThread().isInterrupted() || interrupted) {
            throw new InterruptedException("Solver interrotto");
        }
    }

    /**
     * Log periodico del progresso per debugging
     */
    private void logProgress(int iterationCount) {
        int assignedCount = countAssignedVariables();
        int totalVariables = formula.getVariableCount();

        LOGGER.fine(String.format("Iterazione %d - Decisioni: %d, Conflitti: %d, Assegnate: %d/%d",
                iterationCount, decisionCount, conflictCount, assignedCount, totalVariables));
    }

    //endregion

    //region UNIT PROPAGATION

    /**
     * UNIT PROPAGATION: propaga automaticamente clausole unitarie.
     */
    private PropagationResult performUnitPropagation() {
        List<List<Integer>> allClauses = getAllActiveClauses();
        boolean progressMade;
        int propagationRounds = 0;

        LOGGER.fine("Inizio unit propagation");

        do {
            progressMade = false;
            propagationRounds++;

            if (propagationRounds > 1000) {
                LOGGER.warning("Unit propagation interrotta: possibile loop infinito");
                break;
            }

            for (List<Integer> clause : allClauses) {
                if (interrupted) {
                    return PropagationResult.success();
                }

                ClauseEvaluationResult evaluation = evaluateClause(clause);

                switch (evaluation.getStatus()) {
                    case SATISFIED:
                        continue;

                    case FALSIFIED:
                        // CONFLITTO RILEVATO
                        LOGGER.fine("Conflitto in clausola: " + clause);
                        List<Integer> justifyingClause = findJustifyingClauseForConflict(clause);
                        return PropagationResult.conflict(clause, justifyingClause);

                    case UNIT:
                        // PROPAGAZIONE UNITARIA
                        if (propagateUnitClause(clause, evaluation.getUnitLiteral())) {
                            progressMade = true;
                            LOGGER.finest("Propagazione: " + evaluation.getUnitLiteral() + " da " + clause);
                        }
                        //return PropagationResult.success();
                        break;

                    case UNRESOLVED:
                        continue;
                }
            }

            LOGGER.finest("Round propagazione " + propagationRounds + " - progresso: " + progressMade);

        } while (progressMade && !interrupted);

        LOGGER.fine("Unit propagation completata dopo " + propagationRounds + " round");
        return PropagationResult.success();
    }

    /**
     * Raccoglie tutte le clausole attive (originali + apprese)
     */
    private List<List<Integer>> getAllActiveClauses() {
        List<List<Integer>> allClauses = new ArrayList<>(formula.getClauses());
        allClauses.addAll(learnedClauses);
        return allClauses;
    }

    /**
     * Valuta lo stato di una clausola rispetto agli assegnamenti correnti.
     */
    private ClauseEvaluationResult evaluateClause(List<Integer> clause) {
        int unassignedCount = 0;
        Integer unassignedLiteral = null;

        for (Integer literal : clause) {
            Integer variable = Math.abs(literal);
            AssignedLiteral assignment = assignedValues.get(variable);

            if (assignment == null) {
                // Letterale non assegnato
                unassignedCount++;
                unassignedLiteral = literal;
            } else {
                // Calcola valore del letterale
                boolean literalValue = assignment.getValue();
                if (literal < 0) {
                    literalValue = !literalValue; // Negazione
                }

                if (literalValue) {
                    // Letterale vero → clausola soddisfatta
                    return ClauseEvaluationResult.satisfied();
                }
            }
        }

        // Determina stato finale
        if (unassignedCount == 0) {
            return ClauseEvaluationResult.falsified(); // Tutti falsi = conflitto
        } else if (unassignedCount == 1) {
            return ClauseEvaluationResult.unit(unassignedLiteral); // Unit clause
        } else {
            return ClauseEvaluationResult.unresolved(); // Multiple non assegnati
        }
    }

    /**
     * Propaga una clausola unitaria assegnando l'unico letterale libero.
     */
    private boolean propagateUnitClause(List<Integer> clause, Integer unitLiteral) {
        Integer variable = Math.abs(unitLiteral);
        Boolean value = unitLiteral > 0;

        // Verifica se già assegnata
        AssignedLiteral existingAssignment = assignedValues.get(variable);
        if (existingAssignment != null) {
            return false; // Già assegnata
        }

        // Crea nuovo assegnamento di implicazione
        AssignedLiteral newAssignment = new AssignedLiteral(variable, value, false, clause);
        assignedValues.put(variable, newAssignment);
        decisionStack.addImpliedLiteral(variable, value, clause);
        statistics.incrementPropagations();

        LOGGER.fine("Propagazione unitaria: " + variable + " = " + value + " da " + clause);
        return true;
    }

    /**
     * Trova la clausola che ha giustificato l'ultimo assegnamento nel conflitto.
     */
    private List<Integer> findJustifyingClauseForConflict(List<Integer> conflictClause) {
        // Trova l'ultima implicazione tra i letterali del conflitto
        AssignedLiteral lastPropagation = null;
        int lastLevel = -1;

        for (Integer literal : conflictClause) {
            Integer variable = Math.abs(literal);
            AssignedLiteral assignment = assignedValues.get(variable);

            if (assignment != null && assignment.isImplication()) {
                int level = getLevelForVariable(variable);
                if (level >= lastLevel) {
                    lastLevel = level;
                    lastPropagation = assignment;
                }
            }
        }

        return lastPropagation != null ? lastPropagation.getAncestorClause() : null;
    }

    //endregion

    //region CONFLICT ANALYSIS CORRETTO

    /**
     * CONFLICT ANALYSIS CORRETTO: implementa la "spiegazione" come descritto
     */
    private ConflictAnalysisResult performConflictAnalysis(List<Integer> conflictClause,
                                                           List<Integer> justifyingClause) {
        LOGGER.fine("=== CONFLICT ANALYSIS CON SPIEGAZIONE ===");
        LOGGER.fine("Clausola conflitto: " + conflictClause);
        LOGGER.fine("Clausola giustificante: " + justifyingClause);

        conflictCount++;
        statistics.incrementConflicts();

        // Aggiorna contatori VSIDS
        updateVSIDSCountersAfterConflict(conflictClause);

        // Esegui spiegazione tra clausola giustificante e clausola di conflitto
        List<Integer> explanation = performExplanation(justifyingClause, conflictClause);

        LOGGER.fine("Risultato spiegazione: " + explanation);

        // Registra passo di spiegazione per la prova
        proofGenerator.recordResolutionStep(justifyingClause, conflictClause, explanation);

        // Verifica se abbiamo inconsistenza (clausola vuota)
        if (explanation.isEmpty()) {
            LOGGER.info("Clausola vuota derivata - Formula UNSAT");
            return ConflictAnalysisResult.unsatisfiable();
        }

        // Calcola livello di backtrack basato sul tipo di explanation
        int backtrackLevel = calculateBacktrackLevel(explanation);
        ConflictAnalysisResult ricalcolo = ConflictAnalysisResult.backtrack(explanation, backtrackLevel);

        // Verifica inconsistenza con letterali contraddittori
        if (isInconsistentWithCurrentAssignments(explanation)) {
            LOGGER.info("Inconsistenza rilevata con assegnamenti correnti - Formula UNSAT");

            // Trova il letterale contraddittorio per generare clausola vuota finale
            List<Integer> contradictoryClause = findContradictoryClause(explanation);
            if (contradictoryClause != null) {
                proofGenerator.recordResolutionStep(explanation, contradictoryClause, Collections.emptyList());
            }

            return ConflictAnalysisResult.unsatisfiable();
        }


        return  ricalcolo;
        //return ConflictAnalysisResult.backtrack(explanation, backtrackLevel);
    }

    /**
     * SPIEGAZIONE: implementa l'algoritmo corretto di spiegazione
     */
    private List<Integer> performExplanation(List<Integer> clause1, List<Integer> clause2) {
        LOGGER.finest("Spiegazione tra: " + clause1 + " e " + clause2);

        Set<Integer> result = new HashSet<>();

        // Aggiungi letterali da clause1
        if (clause1 != null) {
            for (Integer literal : clause1) {
                result.add(literal);
            }
        }

        // Aggiungi letterali da clause2, rimuovendo quelli di segno opposto
        if (clause2 != null) {
            for (Integer literal : clause2) {
                if (result.contains(-literal)) {
                    // Letterali di segno opposto - rimuovi entrambi
                    result.remove(-literal);
                } else {
                    // Letterale non contraddittorio - aggiungi
                    result.add(literal);
                }
            }
        }

        List<Integer> explanationResult = new ArrayList<>(result);
        explanationResult.sort(Integer::compareTo);

        LOGGER.finest("Spiegazione completata: " + explanationResult);
        return explanationResult;
    }

    /**
     * Verifica se explanation è inconsistente con assegnamenti correnti
     */
    private boolean isInconsistentWithCurrentAssignments(List<Integer> explanation) {
        for (Integer literal : explanation) {
            Integer variable = Math.abs(literal);
            AssignedLiteral assignment = assignedValues.get(variable);
            ArrayList level0 = decisionStack.getLiteralsAtLevel(0);

            if(level0.size() == 0){
                return false;
            }
            if (assignment != null) {
                boolean expectedValue = literal > 0;
                if (assignment.getValue() != expectedValue) {
                    LOGGER.fine("Inconsistenza trovata: " + variable + " attuale=" +
                            assignment.getValue() + " richiesto=" + expectedValue);
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Trova clausola contraddittoria per generazione clausola vuota finale
     */
    private List<Integer> findContradictoryClause(List<Integer> explanation) {
        for (Integer literal : explanation) {
            Integer variable = Math.abs(literal);
            AssignedLiteral assignment = assignedValues.get(variable);

            if (assignment != null) {
                boolean expectedValue = literal > 0;
                if (assignment.getValue() != expectedValue) {
                    // Trova clausola unitaria contraddittoria
                    return Arrays.asList(-literal);
                }
            }
        }
        return null;
    }

    /**
     * Calcola livello di backtrack corretto
     */
    private int calculateBacktrackLevel(List<Integer> explanation) {
        if (explanation.size() == 1) {
            // Caso 1: singolo letterale -> livello 0 (auto-giustificato)
            return 0;
        } else {
            // Caso 2: disgiunzione -> livello dove letterale asserito è indefinito
            // e gli altri sono falsi
            return findAssertionLevel(explanation);
        }
    }

    /**
     * Trova livello appropriato per assertion di clausola appresa
     */
    private int findAssertionLevel(List<Integer> learnedClause) {
        int currentLevel = decisionStack.size() - 1;

        // Per semplicità, backtrack di un livello per permettere assertion
        return Math.max(0, currentLevel - 1);
    }

    /**
     * Aggiorna contatori VSIDS dopo conflitto
     */
    private void updateVSIDSCountersAfterConflict(List<Integer> conflictClause) {
        for (Integer literal : conflictClause) {
            vsidsCounter.merge(literal, 1, Integer::sum);
        }
    }

    //endregion

    //region APPRENDIMENTO E BACKTRACKING

    /**
     * Esegue apprendimento clausola e backtracking
     */
    private void performLearningAndBacktrack(ConflictAnalysisResult analysisResult) {
        List<Integer> learnedClause = analysisResult.getLearnedClause();
        int backtrackLevel = analysisResult.getBacktrackLevel();

        // Apprendi clausola
        learnNewClause(learnedClause);

        // Esegui backtrack
        performBacktrack(backtrackLevel);

        // Applica assertion se necessario
        applyAssertion(learnedClause, backtrackLevel);
    }

    /**
     * Apprende una nuova clausola
     */
    private void learnNewClause(List<Integer> learnedClause) {
        if (learnedClause == null || learnedClause.isEmpty()) {
            return;
        }

        if (!isDuplicateClause(learnedClause)) {
            learnedClauses.add(new ArrayList<>(learnedClause));
            statistics.incrementLearnedClauses();
            LOGGER.fine("Clausola appresa: " + learnedClause);
        }
    }

    /**
     * Verifica se una clausola è duplicata
     */
    private boolean isDuplicateClause(List<Integer> clause) {
        for (List<Integer> existing : formula.getClauses()) {
            if (clausesEqual(clause, existing)) {
                return true;
            }
        }

        for (List<Integer> existing : learnedClauses) {
            if (clausesEqual(clause, existing)) {
                return true;
            }
        }

        return false;
    }

    /**
     * Confronta due clausole per uguaglianza
     */
    private boolean clausesEqual(List<Integer> clause1, List<Integer> clause2) {
        if (clause1.size() != clause2.size()) {
            return false;
        }

        Set<Integer> set1 = new HashSet<>(clause1);
        Set<Integer> set2 = new HashSet<>(clause2);

        return set1.equals(set2);
    }

    /**
     * Esegue backtrack al livello specificato
     */
    private void performBacktrack(int targetLevel) {
        int currentLevel = decisionStack.size() - 1;

        LOGGER.fine("Backtrack: " + currentLevel + " → " + targetLevel);

        while (decisionStack.size() > targetLevel + 1) {
            List<AssignedLiteral> removedLevel = decisionStack.deleteLevel();

            for (AssignedLiteral assignment : removedLevel) {
                assignedValues.put(assignment.getVariable(), null);
            }
        }

        statistics.incrementBackjumps();
    }

    /**
     * Applica assertion di clausola appresa al livello corrente
     */
    private void applyAssertion(List<Integer> learnedClause, int level) {
        if (learnedClause.size() == 1) {
            // Clausola unitaria - auto-giustificata
            Integer literal = learnedClause.get(0);
            Integer variable = Math.abs(literal);
            Boolean value = literal > 0;

            if (assignedValues.get(variable) == null) {
                AssignedLiteral assertion = new AssignedLiteral(variable, value, false, learnedClause);
                assignedValues.put(variable, assertion);
                decisionStack.addImpliedLiteral(variable, value, learnedClause);

                LOGGER.fine("Assertion applicata: " + variable + " = " + value + " (auto-giustificata)");
            }
        }
    }

    //endregion

    //region DECISION MAKING

    /**
     * Sceglie prossima variabile da assegnare usando VSIDS
     */
    private void makeNextDecision() {
        LOGGER.fine("Ricerca prossima variabile per decisione");

        for (Map.Entry<Integer, AssignedLiteral> entry : assignedValues.entrySet()) {
            Integer variable = entry.getKey();

            if (entry.getValue() == null) {
                Boolean value = selectVariablePolarity(variable);

                decisionCount++;
                statistics.incrementDecisions();

                AssignedLiteral decision = new AssignedLiteral(variable, value, true, null);
                assignedValues.put(variable, decision);
                decisionStack.addDecision(variable, value);

                int currentLevel = decisionStack.size() - 1;
                LOGGER.fine(String.format("DECISIONE #%d: %d = %s @ livello %d",
                        decisionCount, variable, value, currentLevel));

                return;
            }
        }

        throw new IllegalStateException("Nessuna variabile disponibile per decisione");
    }

    /**
     * Seleziona polarità per variabile basata su VSIDS
     */
    private Boolean selectVariablePolarity(Integer variable) {
        Integer positiveCount = vsidsCounter.getOrDefault(variable, 0);
        Integer negativeCount = vsidsCounter.getOrDefault(-variable, 0);

        return positiveCount >= negativeCount;
    }

    //endregion

    //region VERIFICA SODDISFACIMENTO

    /**
     * Verifica se la formula è completamente soddisfatta
     */
    private boolean problemIsSatisfied() {
        // Prima verifica se tutte le variabili sono assegnate
        if (!areAllVariablesAssigned()) {
            return false;
        }

        // Verifica soddisfacimento clausole originali
        if (!areAllClausesSatisfied(formula.getClauses())) {
            return false;
        }

        // Verifica soddisfacimento clausole apprese
        if (!areAllClausesSatisfied(learnedClauses)) {
            return false;
        }

        return true;
    }

    /**
     * Verifica se tutte le clausole sono soddisfatte
     */
    private boolean areAllClausesSatisfied(List<List<Integer>> clauses) {
        for (List<Integer> clause : clauses) {
            ClauseEvaluationResult evaluation = evaluateClause(clause);

            if (evaluation.getStatus() != ClauseEvaluationResult.Status.SATISFIED) {
                return false;
            }
        }

        return true;
    }

    /**
     * Conta variabili attualmente assegnate
     */
    private int countAssignedVariables() {
        return (int) assignedValues.values().stream()
                .filter(Objects::nonNull)
                .count();
    }

    /**
     * Verifica se tutte le variabili sono assegnate
     */
    private boolean areAllVariablesAssigned() {
        return assignedValues.values().stream().noneMatch(Objects::isNull);
    }

    /**
     * Trova livello di una variabile
     */
    private int getLevelForVariable(Integer variable) {
        for (int level = 0; level < decisionStack.size(); level++) {
            if (decisionStack.getLiteralsAtLevel(level).contains(variable)) {
                return level;
            }
        }
        return -1;
    }

    //endregion

    //region GESTIONE RISULTATO FINALE

    /**
     * Gestisce il risultato finale e genera output appropriato
     */
    private SATResult handleFinalResult(CDCLLoopResult loopResult) {
        statistics.stopTimer();

        LOGGER.info("=== STATISTICHE FINALI ===");
        LOGGER.info("Decisioni: " + decisionCount);
        LOGGER.info("Conflitti: " + conflictCount);
        LOGGER.info("Tempo: " + statistics.getExecutionTimeMs() + " ms");
        LOGGER.info("Variabili: " + formula.getVariableCount());
        LOGGER.info("Clausole: " + formula.getClausesCount());

        switch (loopResult.getType()) {
            case SAT:
                LOGGER.info("=== FORMULA SAT - generazione modello ===");
                Map<String, Boolean> model = generateModel();
                return SATResult.satisfiable(model, statistics);

            case UNSAT:
                LOGGER.info("=== FORMULA UNSAT - generazione prova ===");
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
                throw new IllegalStateException("Tipo risultato non gestito: " + loopResult.getType());
        }
    }

    /**
     * Genera modello finale per formula SAT
     */
    private Map<String, Boolean> generateModel() {
        Map<String, Boolean> model = new HashMap<>();

        LOGGER.fine("Generazione modello finale");

        Map<Integer, String> inverseMapping = createInverseVariableMapping();

        for (int variable = 1; variable <= formula.getVariableCount(); variable++) {
            AssignedLiteral assignment = assignedValues.get(variable);

            String originalVariableName = inverseMapping.get(variable);
            if (originalVariableName == null) {
                originalVariableName = String.valueOf(variable);
                LOGGER.warning("Nome originale non trovato per variabile " + variable);
            }

            if (assignment != null) {
                model.put(originalVariableName, assignment.getValue());
                LOGGER.finest("Modello: " + originalVariableName + " = " + assignment.getValue());
            } else {
                model.put(originalVariableName, false); // Default false
                LOGGER.finest("Modello: " + originalVariableName + " = false (default)");
            }
        }

        LOGGER.info("Modello generato con " + model.size() + " variabili");
        return model;
    }

    //endregion

    //region CLASSI DI SUPPORTO E RISULTATI

    /**
     * Risultato della propagazione unitaria
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
     * Risultato della valutazione di una clausola
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
     * Risultato del conflict analysis
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
            return new ConflictAnalysisResult(true, null, -1);
        }

        public static ConflictAnalysisResult backtrack(List<Integer> learnedClause, int level) {
            return new ConflictAnalysisResult(false, learnedClause, level);
        }
    }

    /**
     * Risultato del loop principale CDCL
     */
    private static class CDCLLoopResult {
        public enum Type { SAT, UNSAT, TIMEOUT, INTERRUPTED }

        private final Type type;

        private CDCLLoopResult(Type type) {
            this.type = type;
        }

        public Type getType() { return type; }

        public static CDCLLoopResult sat() {
            return new CDCLLoopResult(Type.SAT);
        }

        public static CDCLLoopResult unsat() {
            return new CDCLLoopResult(Type.UNSAT);
        }

        public static CDCLLoopResult timeout() {
            return new CDCLLoopResult(Type.TIMEOUT);
        }

        public static CDCLLoopResult interrupted() {
            return new CDCLLoopResult(Type.INTERRUPTED);
        }
    }

    //endregion
}