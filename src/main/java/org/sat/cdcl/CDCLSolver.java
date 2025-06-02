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
     * Logger per tracciamento dettagliato delle operazioni del solutore
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
    private SATStatistics statistics;

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

        // Si configura il ProofGenerator con il mapping delle variabili
        Map<Integer, String> inverseMapping = createInverseVariableMapping();
        proofGenerator.setVariableMapping(inverseMapping);

        LOGGER.fine("ProofGenerator configurato con mapping: " + inverseMapping);

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

        // Si avvia un timer
        this.statistics = new SATStatistics();

        try {
            // TODO: NON SERVE QUESTA FASE DI PREPROCESSING, PERCHÈ BLOCCA SUBITO SE È UNSAT,
            //  E NON FORNISCE LA PROVA
            // FASE: Preprocessing con unit propagation iniziale
            /*if (!performInitialPreprocessing()) {
                return createUnsatResult("Conflitto durante preprocessing iniziale");
            }*/

            // FASE 1: Loop principale CDCL
            CDCLLoopResult loopResult = executeCDCLMainLoop();

            // FASE 2: Gestione risultato finale
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
     * Esegue il loop principale dell'algoritmo CDCL con logica UNSAT corretta
     *
     * @return risultato del loop principale
     * @throws InterruptedException se il solver viene interrotto
     */
    private CDCLLoopResult executeCDCLMainLoop() throws InterruptedException {
        LOGGER.fine("=== INIZIO LOOP PRINCIPALE CDCL ===");

        int iterationCount = 0;
        final int MAX_ITERATIONS = 1_000_000; // Limite sicurezza

        while (!interrupted) {
            iterationCount++;

            // Controllo iterazioni per sicurezza
            if (iterationCount > MAX_ITERATIONS) {
                LOGGER.warning("Raggiunto limite massimo iterazioni: " + MAX_ITERATIONS);
                return CDCLLoopResult.timeout();
            }

            // Controllo interruzione
            checkForInterruption();

            // Controllo limiti di sicurezza
            if (hasReachedSafetyLimits()) {
                LOGGER.warning("Raggiunti limiti di sicurezza - decisioni: " + decisionCount +
                        ", conflitti: " + conflictCount);
                return CDCLLoopResult.timeout();
            }

            // STEP 1: Unit Propagation SEMPRE PRIMA (BCP - Boolean Constraint Propagation)
            LOGGER.finest("Unit propagation per iterazione " + iterationCount);
            PropagationResult propagationResult = performUnitPropagation();

            if (propagationResult.hasConflict()) {
                // *** CORREZIONE PRINCIPALE: Controllo livello DURANTE il conflitto ***
                int currentLevel = decisionStack.size() - 1;

                LOGGER.fine("Conflitto rilevato al livello " + currentLevel);

                // CASO CRITICO: Conflitto al livello 0 = UNSAT
                if (currentLevel == 0) {
                    LOGGER.info("Conflitto al livello 0 - Formula UNSAT (nessuna decisione da annullare)");

                    // Registra il conflitto finale per la prova
                    if (propagationResult.getJustifyingClause() != null) {
                        List<Integer> emptyClause = performBinaryResolution(
                                propagationResult.getConflictClause(),
                                propagationResult.getJustifyingClause()
                        );
                        proofGenerator.recordResolutionStep(
                                propagationResult.getConflictClause(),
                                propagationResult.getJustifyingClause(),
                                emptyClause
                        );

                        if (emptyClause.isEmpty()) {
                            proofGenerator.recordEmptyClauseDerivation(
                                    propagationResult.getConflictClause(),
                                    propagationResult.getJustifyingClause()
                            );
                        }
                    }

                    return CDCLLoopResult.unsat();
                }

                // CASO NORMALE: Conflitto a livello > 0, procedi con conflict analysis
                ConflictHandlingResult conflictResult = handleConflict(
                        propagationResult.getConflictClause(),
                        propagationResult.getJustifyingClause()
                );

                if (conflictResult.isUnsatisfiable()) {
                    LOGGER.info("Formula UNSAT determinata durante conflict analysis");
                    return CDCLLoopResult.unsat();
                }

                // Controllo backtrack level negativo (altra condizione UNSAT)
                int backtrackLevel = conflictResult.getBacktrackLevel();
                if (backtrackLevel < 0) {
                    LOGGER.info("Backtrack level negativo - Formula UNSAT");
                    return CDCLLoopResult.unsat();
                }

                // Esegui backtrack e continua il loop
                LOGGER.fine("Backtrack a livello " + backtrackLevel);
                performBacktrack(backtrackLevel);

                // Torna all'inizio del loop per una nuova propagazione
                continue;
            }

            // STEP 2: Verifica se il problema è completamente risolto (SAT)
            if (problemIsSatisfied()) {
                LOGGER.info("Formula SAT - tutte le clausole soddisfatte");
                return CDCLLoopResult.sat();
            }

            // STEP 3: Verifica se tutte le variabili sono assegnate
            boolean allVariablesAssigned = areAllVariablesAssigned();
            if (allVariablesAssigned) {
                // Se tutte le variabili sono assegnate e non siamo in SAT,
                // significa che c'è un errore logico
                LOGGER.severe("ERRORE: Tutte le variabili assegnate ma formula non soddisfatta!");
                logDebugInformation();
                return CDCLLoopResult.timeout();
            }

            // STEP 4: Decisione (solo se non ci sono conflitti e ci sono variabili libere)
            LOGGER.finest("Presa decisione per iterazione " + iterationCount);
            makeNextDecision();

            // Log periodico per debug
            if (iterationCount % 1000 == 0) {
                LOGGER.fine(String.format("Iterazione %d - Decisioni: %d, Conflitti: %d, Variabili assegnate: %d/%d",
                        iterationCount, decisionCount, conflictCount,
                        countAssignedVariables(), formula.getVariableCount()));
            }

            // Continua il loop con la nuova decisione
        }

        LOGGER.info(String.format("Loop CDCL terminato dopo %d iterazioni - Decisioni: %d, Conflitti: %d",
                iterationCount, decisionCount, conflictCount));

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
     * Esegue lo unit propagation a livello 0 per clausole unitarie originali:
     * identifica e propaga tutte le clausole unitarie presenti nella formula
     * originale prima di iniziare qualsiasi processo decisionale del solutore.
     *
     * @return PropagationResult indicante successo o conflitto rilevato
     */
    private PropagationResult performLevelZeroUnitPropagation() {
        LOGGER.fine("Unit propagation livello 0 - clausole unitarie originali");

        // Itera attraverso tutte le clausole della formula CNF originale
        // alla ricerca di clausole unitarie che forzano assegnamenti
        for (List<Integer> clause : formula.getClauses()) {

            // Verifica se una clausola unitaria ha esattamente un letterale
            if (clause.size() == 1) {

                // Ottiene il letterale unico dalla clausola unitaria (positivo oppure negativo)
                Integer literal = clause.get(0);

                // Estrae l'ID della variabile (sempre positivo)
                Integer variable = Math.abs(literal);

                // Letterale positivo -> variabile = true
                // Letterale negativo -> variabile = false
                Boolean value = literal > 0;

                LOGGER.fine("Clausola unitaria trovata: " + variable + " = " + value);

                // Crea un assegnamento implicato
                AssignedLiteral assignment = new AssignedLiteral(variable, value, false, clause);

                // Aggiorna la mappa globale degli assegnamenti
                assignedValues.put(variable, assignment);

                // Aggiunge l'implicazione al livello 0 del decision stack
                decisionStack.addImpliedLiteral(variable, value, clause);
            }
        }

        /*
         * Dopo aver processato tutte le clausole unitarie originali, si
         * esegue propagazione completa per derivare implicazioni conseguenti
         */


        // Se sono stati fatti assegnamenti (stack non vuoto), allora si
        // esegue unit propagation completa per trovare nuove implicazioni
        if (!decisionStack.isEmpty()) {
            // Si applicano gli assegnamenti appena fatti per derivare
            // ulteriori implicazioni o conflitti
            return performUnitPropagation();
        }

        // Se non c'erano clausole unitarie nella formula originale, allora
        // si restituisce successo per procedere con il processo decisionale
        return PropagationResult.success();
    }

    /**
     * Si applica iterativamente la regola di unit propagation fino a raggiungere
     * un punto fisso (nessuna nuova implicazione derivabile) o fino a rilevare un conflitto.
     *
     * @return PropagationResult con esito ed eventuale clausola di conflitto
     */
    private PropagationResult performUnitPropagation() {
        // Ottiene tutte le clausole attive (originali + apprese)
        List<List<Integer>> allClauses = getAllActiveClauses();

        // Flag per tracking progresso in ogni iterazione
        boolean progressMade;

        // Contatore round per logging e limite sicurezza
        int propagationRounds = 0;

        LOGGER.fine("Inizio unit propagation completa");

        // Continua fino a quando non si possono più derivare nuove implicazioni
        do {
            // Reset flag progresso per il nuovo round
            progressMade = false;
            propagationRounds++;

            if (propagationRounds > 1000) {
                LOGGER.warning("Unit propagation interrotta dopo 1000 round: possibile loop infinito");
                break;
            }

            // Esamina ogni clausola per potenziali propagazioni unitarie
            // TODO: forse l'ordine può influenzare le performance?
            for (List<Integer> clause : allClauses) {

                // Interruzione esterna
                if (interrupted) {
                    return PropagationResult.success();
                }

                // Determina lo stato corrente della clausola rispetto agli assegnamenti attuali
                ClauseEvaluationResult evaluation = evaluateClause(clause);

                switch (evaluation.getStatus()) {

                    case SATISFIED:
                        // Almeno un letterale è vero -> clausola completamente soddisfatta
                        continue; // passa alla clausola successiva

                    case FALSIFIED:
                        // Tutti i letterali della clausola sono falsi -> conflitto
                        LOGGER.fine("Conflitto rilevato in clausola: " + clause);

                        // Trova la clausola giustificante dell'ultimo letterale propagato che causa il conflitto
                        List<Integer> justifyingClause = findJustifyingClauseForConflict(clause);

                        // Registra immediatamente il passo di risoluzione per la prova
                        if (justifyingClause != null && !justifyingClause.isEmpty()) {
                            List<Integer> resolvedClause = performBinaryResolution(clause, justifyingClause);
                            proofGenerator.recordResolutionStep(clause, justifyingClause, resolvedClause);

                            LOGGER.fine("Registrato passo di risoluzione: " + clause + " ⊗ " + justifyingClause + " → " + resolvedClause);

                            // Se deriva clausola vuota, registra esplicitamente
                            if (resolvedClause.isEmpty()) {
                                proofGenerator.recordEmptyClauseDerivation(clause, justifyingClause);
                                LOGGER.info("CLAUSOLA VUOTA DERIVATA - Formula UNSAT provata");
                            }
                        }

                        return PropagationResult.conflict(clause, justifyingClause);

                    case UNIT:
                        /*
                         * Esattamente un letterale non assegnato, tutti gli altri falsi
                         * Questo letterale deve essere vero per soddisfare la clausola
                         */


                        // propagateUnitClause restituisce true se ha fatto un nuovo assegnamento
                        if (propagateUnitClause(clause, evaluation.getUnitLiteral())) {
                            // Un nuovo assegnamento è stato fatto, quindi si segna un progresso
                            progressMade = true;

                            LOGGER.finest("Propagazione unitaria: " + evaluation.getUnitLiteral() +
                                    " da clausola " + clause);

                            /*
                             * Continua con altre clausole nello stesso round per massimizzare
                             * il numero di propagazioni per iterazione (efficienza)
                             *
                             */
                        }
                        break;

                    case UNRESOLVED:
                        // La clausola non è ancora risolvibile, perciò si passa alla clausola successiva
                        continue;
                }
            }

            LOGGER.finest("Round propagazione " + propagationRounds + " completato, progresso: " + progressMade);

            /* Continua se:
             * - È stato fatto progresso in questo round (nuovi assegnamenti)
             * - Il solutore non è stato interrotto
             */
        } while (progressMade && !interrupted);

        LOGGER.fine("Unit propagation completata dopo " + propagationRounds + " round");

        // Punto fisso raggiunto senza conflitti -> propagazione completata
        return PropagationResult.success();
    }

    /**
     * Metodo per identificare la clausola giustificante di un conflitto
     */
    private List<Integer> findJustifyingClauseForConflict(List<Integer> conflictClause) {
        // Trova l'ultimo letterale propagato che rende falsa la clausola di conflitto
        AssignedLiteral lastPropagation = null;
        int lastAssignmentOrder = -1;

        for (Integer literal : conflictClause) {
            Integer variable = Math.abs(literal);
            AssignedLiteral assignment = assignedValues.get(variable);

            if (assignment != null && assignment.isImplication()) {
                // Trova l'ordine di assegnamento (approssimazione con livello stack)
                int assignmentOrder = getLevelForVariable(variable);

                if (assignmentOrder > lastAssignmentOrder) {
                    lastAssignmentOrder = assignmentOrder;
                    lastPropagation = assignment;
                }
            }
        }

        // Restituisce la clausola giustificante dell'ultima propagazione
        return lastPropagation != null ? lastPropagation.getAncestorClause() : null;
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
            // Già assegnata - dovrebbe essere consistente (altrimenti sarebbe conflitto)
            return false;
        }

        // Crea nuova implicazione con la clausola giustificante
        AssignedLiteral newAssignment = new AssignedLiteral(variable, value, false, clause);
        assignedValues.put(variable, newAssignment);
        decisionStack.addImpliedLiteral(variable, value, clause);
        statistics.incrementPropagations();

        LOGGER.fine("Propagazione unit: " + variable + " = " + value + " giustificata da clausola " + clause);
        return true;
    }


    /**
     * Prende la prossima decisione usando l'euristica VSIDS.
     * Si seleziona la variabile non assegnata con il punteggio più alto.
     * Il punteggio di una variabile aumenta ogni volta che appare in un conflitto.
     */
    private void makeNextDecision() {
        LOGGER.fine("Ricerca prossima variabile per decisione");

        // Trova la prima variabile non assegnata nell'ordine VSIDS
        for (Map.Entry<Integer, AssignedLiteral> entry : assignedValues.entrySet()) {
            Integer variable = entry.getKey();

            if (entry.getValue() == null) { // Variabile non assegnata
                // Scegli polarità basata sui contatori VSIDS
                Boolean value = selectVariablePolarity(variable);

                // Incrementa sempre il contatore prima di creare la decisione
                decisionCount++;
                statistics.incrementDecisions();

                // Crea e registra la decisione
                AssignedLiteral decision = new AssignedLiteral(variable, value, true, null);
                assignedValues.put(variable, decision);
                decisionStack.addDecision(variable, value);

                int currentLevel = decisionStack.size() - 1;
                LOGGER.fine(String.format("DECISIONE #%d: variabile %d = %s @ livello %d (VSIDS: +%d/-%d)",
                        decisionCount, variable, value, currentLevel,
                        vsidsCounter.get(variable), vsidsCounter.get(-variable)));

                return;
            }
        }

        throw new IllegalStateException("Nessuna variabile disponibile per decisione - tutte assegnate");
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
     * Gestisce un conflitto applicando 1UIP con conteggio accurato.
     *
     * @param conflictClause clausola che ha causato il conflitto
     * @return risultato dell'analisi con livello di backtrack
     */
    private ConflictHandlingResult handleConflict(List<Integer> conflictClause, List<Integer> justifyingClause) {
        LOGGER.fine("=== INIZIO GESTIONE CONFLITTO #" + (conflictCount + 1) + " ===");
        LOGGER.fine("Clausola conflitto: " + conflictClause);
        LOGGER.fine("Clausola giustificante: " + justifyingClause);

        // Aggiorna statistiche
        this.conflictClause = new ArrayList<>(conflictClause);
        conflictCount++;
        statistics.incrementConflicts();

        LOGGER.info(String.format("CONFLITTO #%d rilevato (Decisioni: %d)", conflictCount, decisionCount));

        // Aggiorna contatori VSIDS per tutte le variabili nel conflitto
        updateVSIDSCountersAfterConflict();

        // Se non è stato già registrato durante la propagazione, registralo ora
        if (justifyingClause != null && !justifyingClause.isEmpty()) {
            List<Integer> initialResolution = performBinaryResolution(conflictClause, justifyingClause);

            // Registra il passo solo se non già fatto
            if (!proofGenerator.hasEmptyClause() || !initialResolution.isEmpty()) {
                proofGenerator.recordResolutionStep(conflictClause, justifyingClause, initialResolution);

                if (initialResolution.isEmpty()) {
                    proofGenerator.recordEmptyClauseDerivation(conflictClause, justifyingClause);
                    LOGGER.info("CLAUSOLA VUOTA DERIVATA durante gestione conflitto - Formula UNSAT");
                    return ConflictHandlingResult.unsatisfiable();
                }
            }
        }

        // Esegui analisi 1UIP per il backtracking
        ConflictAnalysisResult analysisResult = performFirstUIPAnalysis();

        if (analysisResult.isUnsatisfiable()) {
            LOGGER.info("=== FORMULA UNSAT - conflict analysis conferma insoddisfacibilità ===");
            return ConflictHandlingResult.unsatisfiable();
        }

        // Controlla UNSAT prima di apprendere
        List<Integer> learnedClause = analysisResult.getLearnedClause();

        // Verifica se la clausola appresa è complementare a una esistente
        List<Integer> complementaryClause = findComplementaryClause(learnedClause);

        if (complementaryClause != null) {
            LOGGER.info("Clausola appresa complementare trovata - derivazione clausola vuota");
            LOGGER.info("Clausola da apprendere: " + learnedClause);
            LOGGER.info("Clausola complementare: " + complementaryClause);

            // Deriva la clausola vuota
            List<Integer> emptyClause = performBinaryResolution(learnedClause, complementaryClause);
            proofGenerator.recordResolutionStep(learnedClause, complementaryClause, emptyClause);

            if (emptyClause.isEmpty()) {
                proofGenerator.recordEmptyClauseDerivation(learnedClause, complementaryClause);
                LOGGER.info("CLAUSOLA VUOTA DERIVATA - Formula UNSAT");
                return ConflictHandlingResult.unsatisfiable();
            }
        }

        // Se non è UNSAT, apprendi la clausola normalmente
        learnNewClause(learnedClause);

        // Controlla se l'apprendimento ha causato UNSAT
        if (proofGenerator.hasEmptyClause()) {
            LOGGER.info("Clausola vuota derivata durante apprendimento - Formula UNSAT");
            return ConflictHandlingResult.unsatisfiable();
        }

        int backtrackLevel = analysisResult.getBacktrackLevel();
        LOGGER.fine(String.format("=== CONFLITTO #%d RISOLTO - backtrack a livello %d ===", conflictCount, backtrackLevel));

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

        LOGGER.fine("Inizio analisi 1UIP - livello corrente: " + currentDecisionLevel);

        // *** CORREZIONE: Se siamo al livello 0, è UNSAT ***
        if (currentDecisionLevel == 0) {
            LOGGER.info("Conflitto al livello 0 durante analisi - UNSAT");
            return ConflictAnalysisResult.unsatisfiable();
        }

        // Si ottiengono gli assegnamenti del livello corrente per l'analisi
        Map<Integer, AssignedLiteral> currentLevelAssignments = getCurrentLevelAssignments();

        int analysisRounds = 0;
        final int MAX_ANALYSIS_ROUNDS = 1000; // Limite di sicurezza

        while (analysisRounds < MAX_ANALYSIS_ROUNDS) {
            analysisRounds++;

            // Conta letterali del livello di decisione corrente nella clausola
            List<Integer> currentLevelLiterals = getCurrentLevelLiterals(currentConflictClause, currentDecisionLevel);

            LOGGER.finest("Round " + analysisRounds + " - letterali livello corrente: " + currentLevelLiterals.size());

            // 1UIP è raggiunto quando c'è esattamente 1 letterale del livello corrente
            if (currentLevelLiterals.size() <= 1) {
                // Crea la clausola appresa
                List<Integer> learnedClause = new ArrayList<>(currentConflictClause);
                int backtrackLevel = calculateBacktrackLevel(learnedClause);

                LOGGER.fine("1UIP raggiunto - clausola appresa: " + learnedClause + ", backtrack: " + backtrackLevel);
                return ConflictAnalysisResult.success(learnedClause, backtrackLevel);
            }

            // Trova la migliore clausola per risoluzione
            List<Integer> resolutionClause = findBestResolutionClause(currentConflictClause, currentLevelAssignments);

            if (resolutionClause.isEmpty()) {
                // Non si può più proseguire: formula insoddisfacibile
                LOGGER.warning("Impossibile continuare analisi conflitto - UNSAT");
                return ConflictAnalysisResult.unsatisfiable();
            }

            // Salva la clausola prima della risoluzione
            List<Integer> beforeResolution = new ArrayList<>(currentConflictClause);

            // Si esegue la risoluzione binaria
            currentConflictClause = performBinaryResolution(currentConflictClause, resolutionClause);

            // Registra sempre ogni passo di risoluzione
            proofGenerator.recordResolutionStep(beforeResolution, resolutionClause, currentConflictClause);

            // *** CORREZIONE: Verifica la clausola vuota (UNSAT) ***
            if (currentConflictClause.isEmpty()) {
                LOGGER.info("Clausola vuota derivata durante analisi - UNSAT");
                // Registra esplicitamente la derivazione della clausola vuota
                proofGenerator.recordEmptyClauseDerivation(beforeResolution, resolutionClause);
                return ConflictAnalysisResult.unsatisfiable();
            }

            // *** CORREZIONE: Se la clausola appresa contiene solo letterali di livelli bassi ***
            // e nessun letterale del livello corrente, potrebbe indicare UNSAT
            List<Integer> remainingCurrentLevelLiterals = getCurrentLevelLiterals(currentConflictClause, currentDecisionLevel);
            if (remainingCurrentLevelLiterals.isEmpty() && currentDecisionLevel > 0) {
                // Tutti i letterali sono di livelli inferiori - verifica se possiamo fare backtrack
                int calculatedBacktrack = calculateBacktrackLevel(currentConflictClause);
                if (calculatedBacktrack < 0) {
                    LOGGER.info("Backtrack level negativo calcolato - UNSAT");
                    return ConflictAnalysisResult.unsatisfiable();
                }
            }
        }

        // Se raggiungiamo il limite di round senza risoluzione
        LOGGER.warning("Raggiunto limite round analisi conflitto - possibile UNSAT");
        return ConflictAnalysisResult.unsatisfiable();
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
     * @return livello di backtrack appropriato (-1 se UNSAT)
     */
    private int calculateBacktrackLevel(List<Integer> learnedClause) {
        if (learnedClause == null) {
            return -1; // Clausola null = UNSAT
        }

        if (learnedClause.isEmpty()) {
            LOGGER.info("Clausola vuota nella backtrack calculation - UNSAT");
            return -1; // Clausola vuota = UNSAT
        }

        if (learnedClause.size() == 1) {
            LOGGER.fine("Clausola unitaria - backtrack al livello 0");
            return 0; // Clausola unitaria = backtrack al livello 0
        }

        // Raccoglie tutti i livelli dei letterali nella clausola
        Set<Integer> levels = new HashSet<>();

        for (Integer literal : learnedClause) {
            Integer variable = Math.abs(literal);
            int level = getLevelForVariable(variable);

            if (level >= 0) {
                levels.add(level);
            } else {
                // Variabile non assegnata - non dovrebbe succedere in una clausola di conflitto
                LOGGER.warning("Variabile non assegnata in clausola appresa: " + variable);
            }
        }

        if (levels.isEmpty()) {
            LOGGER.warning("Nessun livello valido trovato per clausola appresa");
            return -1; // Indica UNSAT
        }

        if (levels.size() < 2) {
            // Solo un livello rappresentato - backtrack al livello 0
            return 0;
        }

        // *** CORREZIONE PRINCIPALE: Logica di backtrack come nel progetto di riferimento ***

        // Ordina in ordine decrescente e prendi il secondo più alto
        List<Integer> sortedLevels = new ArrayList<>(levels);
        sortedLevels.sort(Collections.reverseOrder());

        // Il livello di backtrack è il secondo più alto livello
        // questo garantisce che la clausola appresa diventi unitaria
        int backtrackLevel = sortedLevels.size() > 1 ? sortedLevels.get(1) : 0;

        LOGGER.fine("Livelli nella clausola: " + sortedLevels + " -> backtrack a: " + backtrackLevel);

        // *** CORREZIONE: Verifica che il backtrack level sia valido ***
        int currentLevel = decisionStack.size() - 1;

        if (backtrackLevel >= currentLevel) {
            // Non possiamo fare backtrack a un livello uguale o superiore
            LOGGER.warning("Backtrack level >= current level - possibile UNSAT");
            return Math.max(0, currentLevel - 1);
        }

        // *** CORREZIONE: Implementa la logica di assertion level del progetto di riferimento ***
        // Conta quanti letterali sono definiti fino a ogni livello
        for (int level = 0; level <= backtrackLevel; level++) {
            int definedCount = 0;

            // Conta letterali definiti fino al livello corrente
            for (Integer literal : learnedClause) {
                Integer variable = Math.abs(literal);
                int varLevel = getLevelForVariable(variable);

                if (varLevel >= 0 && varLevel <= level) {
                    definedCount++;
                }
            }

            // Se tutti i letterali tranne uno sono definiti a questo livello,
            // allora questo è il livello corretto per backtrack
            if (definedCount == learnedClause.size() - 1) {
                LOGGER.fine("Assertion level trovato: " + level);
                return level;
            }
        }

        return backtrackLevel;
    }

    /**
     * Apprende una nuova clausola e controlla se genera clausola vuota con clausole esistenti.
     *
     * @param learnedClause clausola da apprendere
     */
    private void learnNewClause(List<Integer> learnedClause) {
        if (learnedClause == null) {
            LOGGER.warning("Tentativo di apprendere clausola null");
            return;
        }

        // Se la clausola è già vuota, è UNSAT
        if (learnedClause.isEmpty()) {
            LOGGER.info("Clausola vuota appresa direttamente - Formula UNSAT");
            proofGenerator.recordEmptyClauseDerivation(new ArrayList<>(), new ArrayList<>());
            return;
        }

        LOGGER.fine("Tentativo apprendimento clausola: " + learnedClause);

        // *** CORREZIONE PRINCIPALE: Controllo clausole complementari ***
        List<Integer> complementaryClause = findComplementaryClause(learnedClause);

        if (complementaryClause != null) {
            LOGGER.info("Trovata clausola complementare! Derivazione clausola vuota:");
            LOGGER.info("Clausola appresa: " + learnedClause);
            LOGGER.info("Clausola complementare: " + complementaryClause);

            // Esegui risoluzione tra le due clausole complementari
            List<Integer> emptyClause = performBinaryResolution(learnedClause, complementaryClause);

            // Registra il passo finale che deriva la clausola vuota
            proofGenerator.recordResolutionStep(learnedClause, complementaryClause, emptyClause);

            if (emptyClause.isEmpty()) {
                proofGenerator.recordEmptyClauseDerivation(learnedClause, complementaryClause);
                LOGGER.info("CLAUSOLA VUOTA DERIVATA - Formula UNSAT confermata");
            }

            return; // Non aggiungere la clausola, abbiamo già UNSAT
        }

        // Evita duplicati
        if (!isDuplicateClause(learnedClause)) {
            // Gestione memoria: rimuovi clausole vecchie se necessario
            manageLearnedClausesMemory();

            // Aggiungi la nuova clausola
            learnedClauses.add(new ArrayList<>(learnedClause));
            statistics.incrementLearnedClauses();

            LOGGER.fine("Clausola appresa: " + learnedClause + " (totale: " + learnedClauses.size() + ")");
        } else {
            LOGGER.fine("Clausola già presente, non aggiunta: " + learnedClause);
        }
    }

    /**
     * Trova una clausola complementare a quella data.
     * Due clausole sono complementari se la loro risoluzione produce la clausola vuota.
     *
     * @param clause clausola per cui cercare complementare
     * @return clausola complementare se trovata, null altrimenti
     */
    private List<Integer> findComplementaryClause(List<Integer> clause) {
        if (clause == null || clause.isEmpty()) {
            return null;
        }

        // Cerca nelle clausole originali
        List<Integer> complement = findComplementaryInList(clause, formula.getClauses());
        if (complement != null) {
            return complement;
        }

        // Cerca nelle clausole apprese
        complement = findComplementaryInList(clause, learnedClauses);
        if (complement != null) {
            return complement;
        }

        return null;
    }

    /**
     * Cerca una clausola complementare in una lista di clausole.
     *
     * @param targetClause clausola target
     * @param clauseList lista in cui cercare
     * @return clausola complementare se trovata
     */
    private List<Integer> findComplementaryInList(List<Integer> targetClause, List<List<Integer>> clauseList) {
        for (List<Integer> existingClause : clauseList) {
            if (areComplementaryClauses(targetClause, existingClause)) {
                return existingClause;
            }
        }
        return null;
    }

    /**
     * Verifica se due clausole sono complementari.
     * Due clausole sono complementari se differiscono per esattamente un letterale
     * e quel letterale ha polarità opposta nelle due clausole.
     *
     * @param clause1 prima clausola
     * @param clause2 seconda clausola
     * @return true se sono complementari
     */
    private boolean areComplementaryClauses(List<Integer> clause1, List<Integer> clause2) {
        if (clause1 == null || clause2 == null) {
            return false;
        }

        // Caso speciale: clausole unitarie complementari
        if (clause1.size() == 1 && clause2.size() == 1) {
            Integer lit1 = clause1.get(0);
            Integer lit2 = clause2.get(0);
            return lit1.equals(-lit2); // Letterali opposti
        }

        // Per clausole più complesse, simula la risoluzione
        List<Integer> resolved = performBinaryResolution(new ArrayList<>(clause1), new ArrayList<>(clause2));
        return resolved.isEmpty(); // Se la risoluzione è vuota, sono complementari
    }

    /**
     * Verifica se una clausola è un duplicato.
     *
     * @param clause clausola da verificare
     * @return true se è duplicata
     */
    private boolean isDuplicateClause(List<Integer> clause) {
        // Controlla nelle clausole originali
        for (List<Integer> existing : formula.getClauses()) {
            if (clausesEqual(clause, existing)) {
                return true;
            }
        }

        // Controlla nelle clausole apprese
        for (List<Integer> existing : learnedClauses) {
            if (clausesEqual(clause, existing)) {
                return true;
            }
        }

        return false;
    }

    /**
     * Verifica se due clausole sono logicamente equivalenti.
     *
     * @param clause1 prima clausola
     * @param clause2 seconda clausola
     * @return true se sono equivalenti
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
     * Esegue backtrack non cronologico con asserzione corretta della clausola appresa.
     *
     * @param targetLevel livello di destinazione del backtrack
     */
    private void performBacktrack(int targetLevel) {
        int currentLevel = decisionStack.size() - 1;

        LOGGER.fine("Backtrack non cronologico: livello " + currentLevel + " → " + targetLevel);

        // Salva la clausola appresa più recente per l'asserzione
        List<Integer> lastLearnedClause = !learnedClauses.isEmpty() ?
                new ArrayList<>(learnedClauses.get(learnedClauses.size() - 1)) : new ArrayList<>();

        // Rimuovi tutti i livelli sopra il target
        while (decisionStack.size() > targetLevel + 1) {
            List<AssignedLiteral> removedLevel = decisionStack.deleteLevel();

            // Rimuovi gli assegnamenti delle variabili del livello rimosso
            for (AssignedLiteral assignment : removedLevel) {
                assignedValues.put(assignment.getVariable(), null);
            }
        }

        // *** CORREZIONE: Asserzione corretta della clausola appresa ***
        if (!lastLearnedClause.isEmpty()) {

            // Trova il letterale di asserzione (quello che diventa unitario al livello target)
            Integer assertionLiteral = findAssertionLiteral(lastLearnedClause, targetLevel);

            if (assertionLiteral != null) {
                Integer variable = Math.abs(assertionLiteral);
                Boolean value = assertionLiteral > 0;

                // Verifica che la variabile non sia già assegnata
                if (assignedValues.get(variable) == null) {
                    AssignedLiteral assertion = new AssignedLiteral(variable, value, false, lastLearnedClause);
                    assignedValues.put(variable, assertion);
                    decisionStack.addImpliedLiteral(variable, value, lastLearnedClause);

                    LOGGER.fine("Asserzione dopo backtrack: " + variable + " = " + value +
                            " giustificata da clausola " + lastLearnedClause);
                } else {
                    // Se la variabile è già assegnata, verifica coerenza
                    AssignedLiteral existing = assignedValues.get(variable);
                    if (!existing.getValue().equals(value)) {
                        LOGGER.warning("Conflitto durante asserzione! Variabile " + variable +
                                " già assegnata a " + existing.getValue() +
                                " ma clausola richiede " + value);

                        // Questo potrebbe indicare UNSAT - registra come conflitto
                        List<Integer> conflictingClause = Arrays.asList(assertionLiteral);
                        List<Integer> emptyClause = performBinaryResolution(
                                conflictingClause,
                                existing.getAncestorClause()
                        );

                        if (emptyClause.isEmpty()) {
                            proofGenerator.recordResolutionStep(
                                    conflictingClause,
                                    existing.getAncestorClause(),
                                    emptyClause
                            );
                            proofGenerator.recordEmptyClauseDerivation(
                                    conflictingClause,
                                    existing.getAncestorClause()
                            );
                        }
                    }
                }
            }
        }

        statistics.incrementBackjumps();
    }

    /**
     * Trova il letterale di asserzione per una clausola appresa al livello target.
     *
     * @param learnedClause clausola appresa
     * @param targetLevel livello di backtrack
     * @return letterale che diventa unitario, null se non trovato
     */
    private Integer findAssertionLiteral(List<Integer> learnedClause, int targetLevel) {
        if (learnedClause.isEmpty()) {
            return null;
        }

        // Se è clausola unitaria, restituisci l'unico letterale
        if (learnedClause.size() == 1) {
            return learnedClause.get(0);
        }

        // Conta quanti letterali sono falsificati al livello target
        int falsifiedCount = 0;
        Integer lastUnfalsified = null;

        for (Integer literal : learnedClause) {
            Integer variable = Math.abs(literal);
            int varLevel = getLevelForVariable(variable);

            if (varLevel > targetLevel) {
                // Letterale non assegnato al livello target
                lastUnfalsified = literal;
            } else if (varLevel >= 0) {
                // Letterale assegnato - verifica se è falsificato
                AssignedLiteral assignment = assignedValues.get(variable);
                if (assignment != null) {
                    boolean literalValue = assignment.getValue();
                    if (literal < 0) {
                        literalValue = !literalValue;
                    }

                    if (!literalValue) {
                        falsifiedCount++;
                    }
                }
            }
        }

        // Se tutti i letterali tranne uno sono falsificati, quello è l'asserzione
        if (falsifiedCount == learnedClause.size() - 1 && lastUnfalsified != null) {
            return lastUnfalsified;
        }

        // Fallback: prendi il primo letterale non assegnato
        for (Integer literal : learnedClause) {
            Integer variable = Math.abs(literal);
            if (assignedValues.get(variable) == null) {
                return literal;
            }
        }

        return null;
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
        LOGGER.finest("Verifica soddisfacimento problema");

        // PASSO 1: Verifica che TUTTE le variabili siano assegnate
        int unassignedVariables = 0;
        for (Map.Entry<Integer, AssignedLiteral> entry : assignedValues.entrySet()) {
            if (entry.getValue() == null) {
                unassignedVariables++;
            }
        }

        if (unassignedVariables > 0) {
            LOGGER.finest("Problema non completamente risolto: " + unassignedVariables + " variabili non assegnate");
            return false; // Ci sono ancora variabili non assegnate
        }

        // PASSO 2: Verifica che TUTTE le clausole originali siano soddisfatte
        if (!areAllClausesSatisfied(formula.getClauses())) {
            LOGGER.warning("Clausole originali non tutte soddisfatte!");
            return false;
        }

        // PASSO 3: Verifica che TUTTE le clausole apprese siano soddisfatte
        if (!areAllClausesSatisfied(learnedClauses)) {
            LOGGER.warning("Clausole apprese non tutte soddisfatte!");
            return false;
        }

        LOGGER.fine("Problema COMPLETAMENTE SODDISFATTO - tutte le variabili assegnate e tutte le clausole vere");
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
     * Metodi di supporto per debug e conteggio
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
     * Log informazioni di debug per diagnostica
     */
    private void logDebugInformation() {
        LOGGER.info("=== INFORMAZIONI DEBUG ===");
        LOGGER.info("Decisioni totali: " + decisionCount);
        LOGGER.info("Conflitti totali: " + conflictCount);
        LOGGER.info("Variabili assegnate: " + countAssignedVariables() + "/" + formula.getVariableCount());
        LOGGER.info("Clausole originali: " + formula.getClausesCount());
        LOGGER.info("Clausole apprese: " + learnedClauses.size());
        LOGGER.info("Livello decisione corrente: " + (decisionStack.size() - 1));

        // Log dettaglio assegnamenti
        if (LOGGER.isLoggable(Level.FINE)) {
            for (Map.Entry<Integer, AssignedLiteral> entry : assignedValues.entrySet()) {
                AssignedLiteral assignment = entry.getValue();
                if (assignment != null) {
                    LOGGER.fine(String.format("Variabile %d = %s (%s)",
                            entry.getKey(), assignment.getValue(),
                            assignment.isDecision() ? "DECISIONE" : "IMPLICAZIONE"));
                } else {
                    LOGGER.fine("Variabile " + entry.getKey() + " = NON_ASSEGNATA");
                }
            }
        }
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
                LOGGER.finest("Modello: " + originalVariableName + " = " + assignment.getValue());

            } else {
                // Le variabili non assegnate sono impostate come false di default
                model.put(originalVariableName, false);
                LOGGER.finest("Modello: " + originalVariableName + " = false (default)");
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
     * Gestisce il risultato finale del loop CDCL con timer accurato.
     *
     * @param loopResult risultato del loop principale
     * @return risultato SAT finale
     */
    private SATResult handleFinalResult(CDCLLoopResult loopResult) {
        // Ferma il timer prima di elaborare il risultato
        statistics.stopTimer();

        // Log statistiche finali per verifica
        LOGGER.info(String.format("=== STATISTICHE FINALI ==="));
        LOGGER.info(String.format("Decisioni: %d", decisionCount));
        LOGGER.info(String.format("Conflitti: %d", conflictCount));
        LOGGER.info(String.format("Tempo: %d ms", statistics.getExecutionTimeMs()));
        LOGGER.info(String.format("Variabili: %d", formula.getVariableCount()));
        LOGGER.info(String.format("Clausole: %d", formula.getClausesCount()));

        switch (loopResult.getType()) {
            case SAT:
                LOGGER.info("=== FORMULA SAT - generazione modello finale ===");
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

        // Il ProofGenerator registra i passi
        String proof = proofGenerator.generateProof();
        int proofSize = proofGenerator.getStepCount();
        statistics.setProofSize(proofSize);

        LOGGER.info("Prova generata con " + proofSize + " passi di risoluzione");

        return SATResult.unsatisfiable(proof, statistics);
    }

    /**
     * Ottiene le statistiche parziali correnti del solutore.
     *
     * @return statistiche parziali correnti
     */
    public SATStatistics getPartialStatistics() {
        // Crea nuove statistiche con i valori correnti
        SATStatistics partialStats = new SATStatistics();

        // Copia i contatori attuali manualmente
        for (int i = 0; i < decisionCount; i++) {
            partialStats.incrementDecisions();
        }

        for (int i = 0; i < conflictCount; i++) {
            partialStats.incrementConflicts();
        }

        // Imposta dimensione prova
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