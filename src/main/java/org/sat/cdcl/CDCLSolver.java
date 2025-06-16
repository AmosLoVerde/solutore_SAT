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
 * Implementazione dell'algoritmo CDCL con:
 * - Tecnica restart opzionale per prevenzione stalli
 * - Anti-loop VSIDS avanzato per prevenzione cicli
 * - Conflict analysis con flusso ibrido unitario/non-unitario
 * - Timing preciso per misurare solo l'esecuzione CDCL core
 */
public class CDCLSolver {

    /** Logger per tracciamento debug e monitoraggio esecuzione algoritmo CDCL */
    private static final Logger LOGGER = Logger.getLogger(CDCLSolver.class.getName());

    //region STRUTTURE DATI CORE - ALGORITMO CDCL

    /** Formula CNF da risolvere - contiene clausole e mapping variabili originali */
    private final CNFFormula formula;

    /** Stack gerarchico per gestire livelli di decisione e backtracking non-cronologico */
    private final DecisionStack decisionStack;

    /** Mappa variabile -> valore assegnato corrente (null = non assegnata) */
    private final Map<Integer, AssignedLiteral> assignedValues;

    /** Contatori VSIDS per euristica selezione variabili (letterale -> frequenza nei conflitti) */
    private final Map<Integer, Integer> vsidsCounter;

    /** Lista delle clausole apprese durante conflict analysis per migliorare performance */
    private final List<List<Integer>> learnedClauses;

    /** Generatore di prove matematiche per formule UNSAT (catena di risoluzioni) */
    private final ProofGenerator proofGenerator;

    /** Set variabili già scelte in decisioni precedenti - previene cicli infiniti nell'euristica */
    private final Set<Integer> alreadyChosenVariables;

    //endregion


    //region STATO ESECUZIONE E MONITORAGGIO

    /** Raccoglitore statistiche dettagliate di performance (tempo, decisioni, conflitti) */
    private SATStatistics statistics;

    /** Tecnica restart opzionale - null se disabilitata, attiva per prevenire stalli */
    private RestartTechnique restartTechnique;

    /** Flag thread-safe per interruzione controllata da timeout esterni */
    private volatile boolean interrupted = false;

    // Contatori eventi principali dell'algoritmo CDCL
    /** Numero totale di conflitti rilevati durante la risoluzione */
    private int conflictCount = 0;

    /** Numero totale di decisioni euristiche prese */
    private int decisionCount = 0;

    /** Statistiche dettagliate per ogni singola decisione euristica */
    private final List<DecisionStatistics> decisionStatisticsList = new ArrayList<>();

    /**
     * Metriche per singola decisione - traccia propagazioni, conflitti, spiegazioni
     * e clausole apprese generate dalla specifica decisione
     */
    private static class DecisionStatistics {
        int decisionNumber;     // Numero progressivo della decisione
        int propagations;       // Unit propagations scatenate da questa decisione
        int conflicts;          // Conflitti emersi da questa decisione
        int explanations;       // Spiegazioni generate dai conflitti
        int learnedClauses;     // Clausole apprese dai conflitti

        DecisionStatistics(int decisionNumber) {
            this.decisionNumber = decisionNumber;
        }
    }

    //endregion


    //region INIZIALIZZAZIONE

    /**
     * Costruttore principale del solutore CDCL con configurazione di reinizio opzionale.
     *
     * Inizializza tutte le strutture dati necessarie per l'algoritmo CDCL:
     * - Formula CNF da risolvere
     * - Stack per gestione livelli di decisione e backtracking
     * - Mappa degli assegnamenti variabili
     * - Contatori VSIDS per euristica selezione variabili
     * - Sistema di generazione prove per formule UNSAT
     * - Tecnica di reinizio opzionale per prevenire stalli
     *
     * @param cnfConverter formula in formato albero da convertire in CNF
     * @param enableRestart true per abilitare il reinizio automatico, false per il solutore
     */
    public CDCLSolver(CNFConverter cnfConverter, boolean enableRestart) {
        System.out.println("\n\n<<< INIZIALIZZAZIONE SOLUTORE CDCL >>>");

        // FASE 1: Inizializzazione strutture dati algoritmo CDCL
        this.formula = new CNFFormula(cnfConverter);                    // Converte e memorizza la formula CNF
        this.decisionStack = new DecisionStack();                       // Stack per backtracking non-cronologico
        this.assignedValues = initializeVariableAssignments();          // Mappa var -> valore ordinata per frequenza
        this.vsidsCounter = initializeVSIDSCounters();                  // Contatori letterali per euristica dinamica
        this.learnedClauses = new ArrayList<>();                        // Clausole apprese durante conflict analysis
        this.alreadyChosenVariables = new HashSet<>();                  // Anti-loop: variabili già tentate

        // FASE 2: Sistema generazione prove matematiche per UNSAT
        this.proofGenerator = new ProofGenerator();                                 // Generatore catena risoluzioni
        this.proofGenerator.setVariableMapping(createInverseVariableMapping());     // Mapping ID -> nomi originali

        // FASE 3: Configurazione restart opzionale (null se disabilitato)
        if (enableRestart) {
            this.restartTechnique = new RestartTechnique();                         // Attiva restart automatici
            System.out.println("[I] Tecnica del reinizio abilitata!");
        }

        // FASE 4: Validazione configurazione e logging informativo
        logInitializationInfo();                                                    // Log dettagli formula (clausole/variabili)
        System.out.println("<<< SOLUTORE CDCL PRONTO >>>");
    }

    /**
     * Inizializza la mappa degli assegnamenti variabili ordinata per frequenza di apparizione.
     *
     * Le variabili che appaiono più frequentemente nelle clausole vengono processate per prime
     * durante la ricerca, migliorando l'efficienza dell'euristica VSIDS e riducendo il numero di
     * decisioni necessarie.
     *
     * @return LinkedHashMap ordinata: variabile -> AssignedLiteral (inizialmente null = non assegnata)
     *         Ordine: dalla variabile più frequente alla meno frequente
     */
    private LinkedHashMap<Integer, AssignedLiteral> initializeVariableAssignments() {

        // FASE 1: Conteggio frequenze - inizializza contatori a zero per tutte le variabili
        Map<Integer, Integer> frequencies = new HashMap<>();
        for (int var = 1; var <= formula.getVariableCount(); var++) {
            frequencies.put(var, 0);                                                          // Ogni variabile inizia con frequenza 0
        }

        // FASE 2: Scansione clausole - conta apparizioni di ogni variabile
        for (List<Integer> clause : formula.getClauses()) {                                   // Per ogni clausola della formula
            for (Integer literal : clause) {                                                  // Per ogni letterale nella clausola
                frequencies.merge(Math.abs(literal), 1, Integer::sum);                  // Incrementa freq. della variabile (ignora segno)
            }
        }

        // FASE 3: Ordinamento per frequenza decrescente - variabili più frequenti => priorità maggiore
        LinkedHashMap<Integer, AssignedLiteral> ordered = new LinkedHashMap<>();
        frequencies.entrySet().stream()                                                       // Stream delle coppie (variabile, frequenza)
                .sorted(Map.Entry.<Integer, Integer>comparingByValue().reversed())            // Ordina: freq. alta → bassa
                .forEach(entry -> ordered.put(entry.getKey(), null));     // Inserisce var → null (non assegnata)

        return ordered;         // Mappa ordinata pronta per l'algoritmo CDCL
    }

    /**
     * Inizializza i contatori VSIDS per l'euristica dinamica di selezione delle variabili
     * durante la fase di decisione.
     *
     * @return HashMap con mapping: letterale -> contatore conflitti
     *         Esempio: var=5 genera entries: {5 -> 0, -5 -> 0} per letterale positivo e negativo
     */
    private Map<Integer, Integer> initializeVSIDSCounters() {

        // Mappa letterale -> numero di apparizioni nei conflitti (inizialmente 0)
        Map<Integer, Integer> counters = new HashMap<>();

        // Per ogni variabile della formula, crea contatori per entrambe le polarità
        for (Integer variable : assignedValues.keySet()) {              // Itera su tutte le variabili
            counters.put(variable, 0);                                  // Letterale positivo: var → 0
            counters.put(-variable, 0);                                 // Letterale negativo: -var → 0
        }

        return counters;                                                // Contatori pronti per aggiornamenti durante conflitti
    }

    /**
     * Crea il mapping inverso da ID numerico a nome variabile originale per la generazione
     * di prove e modelli leggibili dall'utente.
     *
     * @return HashMap con mapping: ID numerico → nome variabile originale
     */
    private Map<Integer, String> createInverseVariableMapping() {

        // Mappa ID -> nome per riconversione finale (prove UNSAT e modelli SAT)
        Map<Integer, String> inverse = new HashMap<>();

        // Inverte il mapping nome -> ID originale della formula in ID -> nome
        formula.getVariableMapping()                                                    // Ottiene mapping originale: nome -> ID
                .forEach((name, id) -> inverse.put(id, name));             // Inverte in: ID -> nome

        return inverse;       // Mapping inverso pronto per output leggibili
    }

    /**
     * Registra le informazioni diagnostiche sulla formula caricata per monitoraggio e debug.
     *
     * Indicatore dd rapporto clausole/variabili (C/V ratio) per conoscere la complessità
     * della formula SAT:
     * - Ratio < 2.0: Formula sparsa, ossia è più facile da risolvere
     * - Ratio 2.0-4.0: Complessità media, ossia il comportamento è bilanciato
     * - Ratio > 4.0: Formula densa, cioè è potenzialmente più difficile e lenta
     *
     */
    private void logInitializationInfo() {

        // Estrae metriche di base della formula CNF
        int clauses = formula.getClausesCount();                            // Numero totale clausole
        int variables = formula.getVariableCount();                         // Numero totale variabili

        // Calcola rapporto clausole/variabili (protezione divisione per zero)
        double ratio = variables > 0 ? (double) clauses / variables : 0;    // C/V ratio per analisi complessità

        // Log informativo con metriche formula per diagnostica
        System.out.printf("[I] Formula: %d clausole, %d variabili (C/V: %.2f)\n", clauses, variables, ratio);
    }

    //endregion


    //region INTERFACCIA PUBBLICA

    /**
     * Metodo principale per la risoluzione di formule SAT utilizzando l'algoritmo CDCL.
     *
     * Esegue il ciclo completo di risoluzione:
     * 1. Inizializza il sistema di statistiche e timing
     * 2. Esegue l'algoritmo CDCL core con timing
     * 3. Genera risultato finale (SAT con modello, UNSAT con prova, oppure timeout)
     * 4. Gestisce le interruzioni esterne ed errori critici
     *
     * @return SATResult contenente:
     *         - Se SAT: modello (assegnamenti variabili) + statistiche
     *         - Se UNSAT: prova matematica (catena risoluzioni) + statistiche
     * @throws RuntimeException per timeout o errori critici non recuperabili
     */
    public SATResult solve() {
        System.out.println("\n\n=== AVVIO RISOLUZIONE CDCL ===");

        // Inizializza le statistiche
        this.statistics = new SATStatistics();

        try {
            // Si misura solo l'esecuzione dell'algoritmo CDCL
            statistics.startCDCLTimer();                                // Avvia cronometro prima di CDCL
            CDCLExecutionResult result = executeCDCLMainAlgorithm();    // Esegue algoritmo CDCL completo
            statistics.stopTimer();                                     // Ferma cronometro dopo CDCL

            // Genera output finale basato su risultato algoritmo (SAT/UNSAT/TIMEOUT)
            return generateFinalResult(result);

        } catch (InterruptedException e) {
            // Gestione timeout esterno controllato
            statistics.stopTimer();
            return handleInterruption();

        } catch (Exception e) {
            // Gestione errori critici non previsti
            statistics.stopTimer();
            return handleCriticalError(e);
        }
    }

    //endregion


    //region ALGORITMO CDCL PRINCIPALE

    /**
     * Implementa il loop principale dell'algoritmo CDCL (Conflict-Driven Clause Learning).
     *
     * Algoritmo CDCL in 3 fasi cicliche:
     * 1. Unit Propagation: propaga le conseguenze logiche obbligate
     * 2. Analisi dei confitti: se conflitto -> genera clausola appresa + backtrack
     * 3. Decisione: se nessun conflitto -> sceglie prossima variabile tramite euristica
     *
     * Termina quando: formula soddisfatta (SAT), conflitto irrisolvibile (UNSAT),
     * timeout (limite iterazioni), oppure c'è una interruzione esterna.
     *
     * @return CDCLExecutionResult indicante l'esito: SATISFIABLE, UNSATISFIABLE, TIMEOUT, INTERRUPTED
     * @throws InterruptedException se il solver viene interrotto esternamente per timeout
     */
    private CDCLExecutionResult executeCDCLMainAlgorithm() throws InterruptedException {
        LOGGER.fine("=== LOOP PRINCIPALE CDCL ===");

        // INIZIALIZZAZIONE: Configura livello 0 con clausole unitarie della formula originale
        try {
            initializeLevel0WithUnitClauses();                          // Propaga tutte le clausole unitarie iniziali
        } catch (ImmediateUNSATException e) {
            // Caso speciale: clausole unitarie contraddittorie (es: {A} e {!A})
            LOGGER.info("UNSAT immediato: " + e.getMessage());
            return CDCLExecutionResult.unsatisfiable();                 // Formula UNSAT senza bisogno di ricerca
        }

        // Ciclo principale per il CDCL con protezione anti-loop infinito
        int iterations = 0;
        while (!interrupted && iterations < 100_000) {                   // Limite iterazioni per sicurezza
            iterations++;

            // Log progresso periodico per monitoraggio esecuzioni lunghe
            if (iterations % 1000 == 0) {
                logProgress(iterations);                                 // Statistiche ogni 1000 iterazioni
            }

            checkForInterruption();                                     // Verifica un timeout esterno

            // STEP 1: si verifica la soddisfacibilità completa
            if (isFormulaSatisfied()) {
                System.out.println("[I] Formula SAT: tutte le clausole soddisfatte");
                return CDCLExecutionResult.satisfiable();
            }

            // STEP 2: propagazione unitaria e rilevazione dei conflitti
            PropagationResult propResult = executeUnitPropagation();   // Propaga conseguenze obbligate
            if (propResult.hasConflict()) {
                // Genera una spiegazione e ricava la clausola da apprendere
                ConflictAnalysisResult analysis = resolveConflict(
                        propResult.getConflictClause(), propResult.getJustifyingClause());

                if (analysis.isUnsatisfiable()) {
                    System.out.println("[I] Formula UNSAT dall'analisi dei conflitti");
                    return CDCLExecutionResult.unsatisfiable();
                }

                // Apprendimento della clausola + salto all'indietro
                executeLearningAndBacktrack(analysis);
                continue;
            }

            // STEP 3: fase di decisione tramite euristica
            if (!areAllVariablesAssigned()) {
                executeDecisionMaking();               // Sceglie prossima variabile con euristica VSIDS
            }
        }

        // TERMINAZIONE: timeout o tutte variabili sono assegnate
        return iterations >= 100_000 ? CDCLExecutionResult.timeout() :  // Limite iterazioni raggiunto
                CDCLExecutionResult.satisfiable();                      // Tutte variabili assegnate
    }

    //endregion


    //region INIZIALIZZAZIONE DEL LIVELLO 0

    /**
     * Inizializza il livello 0 del decision stack processando tutte le clausole unitarie
     * della formula originale e rilevando contraddizioni immediate.
     *
     * @throws ImmediateUNSATException se rileva clausole unitarie contraddittorie
     */
    private void initializeLevel0WithUnitClauses() {
        System.out.println("Inizializzazione del livello 0 con clausole unitarie");

        // Tracking per rilevamento contraddizioni immediate tra clausole unitarie
        Map<Integer, Boolean> unitValues = new HashMap<>();            // Variabile = valore richiesto da clausola unitaria
        Map<Integer, List<Integer>> unitSources = new HashMap<>();     // Variabile = clausola unitaria che la richiede

        // Scansiona tutte le clausole della formula per identificare quelle unitarie
        for (List<Integer> clause : formula.getClauses()) {
            if (clause.size() == 1) {
                // Estrae informazioni dal letterale unitario
                Integer literal = clause.get(0);                       // Unico letterale nella clausola
                Integer variable = Math.abs(literal);                  // ID variabile (senza segno)
                Boolean value = literal > 0;                           // Polarità: positivo=true, negativo=false

                // Si controllano le contraddizioni immediate
                if (unitValues.containsKey(variable)) {
                    Boolean existing = unitValues.get(variable);       // Valore richiesto dalla clausola precedente
                    if (!existing.equals(value)) {
                        // Ecco rilevata una contraddizione: {A} vs {!A} -> formula immediatamente UNSAT
                        List<Integer> clause1 = unitSources.get(variable);
                        proofGenerator.recordResolutionStep(clause1, clause, new ArrayList<>());
                        conflictCount = 1;                             // Registra conflitto per statistiche
                        statistics.incrementConflicts();
                        throw new ImmediateUNSATException("Clausole unitarie contraddittorie");
                    }
                }

                // Si assegna un valore alla variabile se non è già assegnata
                if (assignedValues.get(variable) == null) {
                    // Crea assegnazione obbligata al livello 0 (implicazione, non decisione)
                    AssignedLiteral assignment = new AssignedLiteral(variable, value, false, clause);
                    assignedValues.put(variable, assignment);                   // Registra l'assegnamento nella mappa globale
                    decisionStack.addImpliedLiteral(variable, value, clause);   // Aggiunge al livello 0 del decision stack

                    // Aggiorna il tracking per controlli successivi
                    unitValues.put(variable, value);                            // Memorizza valore per controlli contraddizioni
                    unitSources.put(variable, new ArrayList<>(clause));         // Memorizza clausola sorgente per prove

                    // Aggiorna statistiche: clausola unitaria = propagazione automatica
                    statistics.incrementPropagations();
                    updateCurrentDecisionStats(stats -> stats.propagations++);
                }
            }
        }
    }

    /**
     * Eccezione specializzata per segnalare che la formula è immediatamente UNSAT
     * senza necessità di eseguire l'algoritmo di ricerca CDCL completo.
     */
    private static class ImmediateUNSATException extends RuntimeException {

        /**
         * Costruttore per eccezione UNSAT immediato con messaggio descrittivo.
         *
         * @param message descrizione della contraddizione rilevata
         */
        ImmediateUNSATException(String message) {
            super(message);                                             // Propaga messaggio a RuntimeException
        }
    }

    //endregion


    //region UNIT PROPAGATION

    /**
     * Esegue unit propagation iterativa fino a raggiungere il punto fisso o conflitto.
     *
     * Algoritmo:
     * 1. Ricava tutte le clausole attive cercando clausole unit
     * 2. Per ogni clausola unit trovata, propaga l'assegnamento obbligato
     * 3. Ripete fino a quando non c'è nessuna nuova propagazione o conflitto
     * 4. Se rileva clausola falsificata allora termina con conflitto
     *
     * @return PropagationResult indicante successo (punto fisso raggiunto)
     *         o conflitto (clausola falsificata + clausola giustificante per analisi)
     */
    private PropagationResult executeUnitPropagation() {

        // Ottiene tutte le clausole da valutare (originali + apprese)
        List<List<Integer>> allClauses = getAllActiveClauses();
        boolean progress;
        int rounds = 0;                                                 // Contatore round per protezione anti-loop

        do {
            progress = false;                                           // Reset flag progresso per nuovo round
            rounds++;

            // Protezione anti-loop infinito (non dovrebbe mai accadere in teoria)
            if (rounds > 1000) {
                System.out.println("[W] Unit propagation interrotta: possibile loop infinito");
                break;
            }

            // Controlla tutte le clausole per trovare propagazioni obbligate
            for (List<Integer> clause : allClauses) {
                if (interrupted) return PropagationResult.success();   // Rispetta l'interruzione esterna

                // Valuta lo stato corrente della clausola con assegnamenti attuali
                ClauseEvaluationResult eval = evaluateClauseState(clause);
                switch (eval.getStatus()) {
                    case SATISFIED -> {         // Clausola soddisfatta
                        continue;
                    }
                    case FALSIFIED -> {         // Conflitto rilevato: tutti letterali sono falsificati
                        List<Integer> justifying = findJustifyingClauseForConflict(clause);     // Cerca l'ultima clausola giustificante
                        return PropagationResult.conflict(clause, justifying);                  // Esegue la risoluzione del conflitto
                    }
                    case UNIT -> {              // Clausola UNIT: un solo letterale non assegnato, quindi la propagazione è obbligata
                        if (propagateUnitClause(clause, eval.getUnitLiteral())) {
                            progress = true;                            // Segnala che è avvenuta una propagazione
                        }
                    }
                    case UNRESOLVED -> {        // Clausola con più letterali liberi, perciò non i può dire nulla
                        continue;
                    }
                }
            }
        } while (progress && !interrupted);

        // Si è raggiunto il punto fisso: nessuna nuova propagazione possibile
        return PropagationResult.success();     // Propagazione completata senza conflitti
    }

    /**
     * Raccoglie tutte le clausole attualmente attive per la valutazione durante unit propagation.
     *
     * @return Lista unificata di tutte le clausole attive da valutare
     *         (non viene applicato alcun filtro di attivazione/disattivazione)
     */
    private List<List<Integer>> getAllActiveClauses() {

        // Inizializza con copia delle clausole originali dalla formula CNF
        List<List<Integer>> all = new ArrayList<>(formula.getClauses());   // Clausole della formula originale

        // Aggiunge tutte le clausole apprese durante l'esecuzione CDCL
        all.addAll(learnedClauses);                                        // Clausole generate dall'analisi dei conflitti

        return all;                                                        // Lista completa per unit propagation
    }

    /**
     * Valuta lo stato corrente di una clausola rispetto agli assegnamenti attuali delle variabili.
     *
     * Analizza ogni letterale nella clausola per determinare se la clausola è:
     * - SATISFIED: almeno un letterale è vero -> clausola soddisfatta
     * - FALSIFIED: tutti letterali sono falsi -> conflitto rilevato
     * - UNIT: esattamente un letterale non assegnato -> propagazione obbligata
     * - UNRESOLVED: più letterali non assegnati -> nessuna azione immediata
     *
     * @param clause clausola da valutare (lista di letterali con segno)
     * @return ClauseEvaluationResult contenente stato e informazioni per unit propagation
     */
    private ClauseEvaluationResult evaluateClauseState(List<Integer> clause) {

        // Contatori per determinare stato clausola
        int unassigned = 0;                                             // Numero letterali non ancora assegnati
        Integer unassignedLiteral = null;                               // Ultimo letterale non assegnato (per clausole unit)

        // Controlla tutti i letterali della clausola
        for (Integer literal : clause) {
            Integer variable = Math.abs(literal);                       // Estrae l'ID della variabile (senza segno)
            AssignedLiteral assignment = assignedValues.get(variable);  // Recupera l'assegnamento corrente

            if (assignment == null) {
                // Il letterale non è assegnato: conta per determinare stato finale
                unassigned++;                                           // Incrementa contatore letterali liberi
                unassignedLiteral = literal;                            // Memorizza per potenziale unit propagation

            } else {
                // Il letterale è assegnato: calcola valore di verità e controlla soddisfacimento
                boolean literalValue = assignment.getValue();           // Valore variabile (true/false)
                if (literal < 0) literalValue = !literalValue;          // Se letterale negativo, allora inverte il valore

                if (literalValue) {
                    return ClauseEvaluationResult.satisfied();          // Almeno un letterale vero
                }
            }
        }

        // Classificazione finale basata sui letterali non assegnati
        return switch (unassigned) {
            case 0 -> ClauseEvaluationResult.falsified();              // Tutti letterali falsi -> CONFLITTO
            case 1 -> ClauseEvaluationResult.unit(unassignedLiteral);  // Un letterale libero -> UNIT PROPAGATION
            default -> ClauseEvaluationResult.unresolved();            // Più letterali liberi -> NESSUNA AZIONE
        };
    }

    /**
     * Propaga l'assegnamento obbligato per una clausola unit (con un solo letterale non assegnato).
     *
     * Esempio: clausola {A, !B, C} con A=false, B=true -> diventa unit su C
     *          -> C deve essere true per soddisfare la clausola
     *
     * @param clause clausola unit che richiede la propagazione
     * @param unitLiteral unico letterale non assegnato nella clausola (con segno)
     * @return true se propagazione effettuata, false se variabile già assegnata
     */
    private boolean propagateUnitClause(List<Integer> clause, Integer unitLiteral) {

        // Estrae le informazioni dal letterale unit per creare assegnamento
        Integer variable = Math.abs(unitLiteral);                       // ID variabile (senza segno)
        Boolean value = unitLiteral > 0;                                // Polarità: positivo=true, negativo=false

        // Si controlla se la variabile è già assegnata
        if (assignedValues.get(variable) != null) {
            return false;
        }

        // Si crea e registra l'implicazione
        AssignedLiteral implication = new AssignedLiteral(variable, value, false, clause);

        assignedValues.put(variable, implication);                      // Registra l'assegnamento nella mappa globale
        decisionStack.addImpliedLiteral(variable, value, clause);       // Aggiunge al livello corrente del decision stack

        // Si aggiornano le statistiche
        statistics.incrementPropagations();
        updateCurrentDecisionStats(stats -> stats.propagations++);

        return true;        // Propagazione completata con successo
    }

    //endregion


    //region CONFLICT ANALYSIS

    /**
     * Risolve un conflitto attraverso l'analisi, apprendimento e reinizio euristico.
     *
     * @param conflictClause clausola falsificata che ha causato il conflitto
     * @param justifyingClause clausola che giustifica il conflitto per la prova
     * @return ConflictAnalysisResult indicante strategia: UNSATISFIABLE, BACKTRACK, o RESTART
     */
    private ConflictAnalysisResult resolveConflict(List<Integer> conflictClause, List<Integer> justifyingClause) {
        System.out.println("Risoluzione del conflitto...");

        // Incrementa contatore conflitti
        conflictCount++;
        statistics.incrementConflicts();
        updateCurrentDecisionStats(stats -> stats.conflicts++);

        // Aggiorna contatori VSIDS
        updateVSIDSCounters(conflictClause);

        // Valuta se effettuare il reinizio
        if (restartTechnique != null && restartTechnique.registerConflictAndCheckRestart()) {
            System.out.println("[I] Reinizio attivo");
            statistics.incrementRestarts();
            return executeRestart();
        }

        // Genera la clausola di spiegazione tramite risoluzione
        List<Integer> explanationClause = generateExplanation(conflictClause, justifyingClause);
        statistics.incrementExplanations();
        updateCurrentDecisionStats(stats -> stats.explanations++);

        // Registra il passo di risoluzione per prova matematica
        proofGenerator.recordResolutionStep(conflictClause, justifyingClause, explanationClause);

        // Controlla se è insoddisfacibile (clausola vuota)
        if (explanationClause.isEmpty()) {
            return ConflictAnalysisResult.unsatisfiable();
        }

        // Gestione in base alla dimensione della clausola di spiegazione
        if (explanationClause.size() == 1) {
            // Caso 1: Clausola unitaria
            return handleUnitClauseLearning(explanationClause);
        } else {
            // Caso 2: Clausola multi-letterale
            return handleNonUnitClauseLearning(explanationClause, conflictClause, justifyingClause);
        }
    }

    /**
     * Gestisce l'apprendimento e il backtrack per clausole unitarie.
     *
     * @param unitClause clausola unitaria appresa dal conflict analysis
     * @return ConflictAnalysisResult con backtrack al livello 0 o UNSATISFIABLE
     */
    private ConflictAnalysisResult handleUnitClauseLearning(List<Integer> unitClause) {

        // Si verifica la consistenza con le clausole apprese in precedenza
        List<Integer> conflicting = checkConsistencyWithLearnedClauses(unitClause);

        if (conflicting != null) {
            // Si è rilevato un conflitto: genera un'ulteriore risoluzione
            List<Integer> finalClause = generateExplanation(unitClause, conflicting);
            proofGenerator.recordResolutionStep(unitClause, conflicting, finalClause);

            // Controlla se la risoluzione produce clausola vuota (UNSAT)
            if (finalClause.isEmpty()) {
                return ConflictAnalysisResult.unsatisfiable();          // Formula UNSAT
            }

            // Aggiorna statistiche per risoluzione aggiuntiva
            statistics.incrementExplanations();
            updateCurrentDecisionStats(stats -> stats.explanations++);
        }

        // Backtrack al livello 0 per la clausola unitaria
        return ConflictAnalysisResult.backtrack(unitClause, 0);
    }

    /**
     * Gestisce l'apprendimento e il backtrack per le clausole multi-letterale.
     * È necessario perché potrebbe dare ancora conflitti sullo stesso livello
     *
     * @param explanationClause clausola multi-letterale da analizzare
     * @param originalConflictClause clausola originale del conflitto (per tracciamento)
     * @param originalJustifyingClause clausola giustificante originale (per tracciamento)
     * @return ConflictAnalysisResult con backtrack appropriato o UNSATISFIABLE
     */
    private ConflictAnalysisResult handleNonUnitClauseLearning(List<Integer> explanationClause,
                                                               List<Integer> originalConflictClause,
                                                               List<Integer> originalJustifyingClause) {

        List<Integer> currentClause = explanationClause;
        int currentLevel = decisionStack.getLevel();

        // Continua a risolvere finché necessario
        while (true) {
            // Cerca conflitti con letterali propagati sullo stesso livello
            List<Integer> conflictingClauseOnLevel = findConflictingClauseOnSameLevel(currentClause, currentLevel);

            if (conflictingClauseOnLevel == null) {
                // Nessun conflitto sullo stesso livello - procedi con il backtrack
                break;
            }

            // Genera nuova spiegazione risolvendo il conflitto
            List<Integer> newExplanation = generateExplanation(currentClause, conflictingClauseOnLevel);
            statistics.incrementExplanations();
            updateCurrentDecisionStats(stats -> stats.explanations++);

            // Registra il passo per la prova
            proofGenerator.recordResolutionStep(currentClause, conflictingClauseOnLevel, newExplanation);

            // Controlla se UNSAT
            if (newExplanation.isEmpty()) {
                return ConflictAnalysisResult.unsatisfiable();
            }

            // Se la nuova spiegazione è unitaria, delega al gestore appropriato
            if (newExplanation.size() == 1) {
                return handleUnitClauseLearning(newExplanation);
            }

            // Continua con la nuova clausola
            currentClause = newExplanation;
        }

        // A questo punto abbiamo una clausola multi-letterale senza conflitti sullo stesso livello
        // Trova il letterale asserito (opposto alla decisione del livello corrente)
        Integer assertedLiteral = findAssertedLiteral(currentClause, currentLevel);

        if (assertedLiteral == null) {
            // Nessun letterale asserito trovato - backtrack al livello precedente
            return ConflictAnalysisResult.backtrack(currentClause, Math.max(0, currentLevel - 1));
        }

        // Trova il livello di backtrack per il letterale asserito
        int backtrackLevel = findBacktrackLevel(currentClause, assertedLiteral, currentLevel);

        // Ritorna il risultato con la clausola appresa e il livello di backtrack
        return ConflictAnalysisResult.backtrack(currentClause, backtrackLevel);
    }


    /**
     * Trova una clausola che entra in conflitto con la clausola data sullo stesso livello.
     *
     * @param clause clausola da verificare
     * @param level livello decisionale corrente
     * @return clausola conflittuale trovata, o null se nessun conflitto
     */
    private List<Integer> findConflictingClauseOnSameLevel(List<Integer> clause, int level) {
        // Ottieni tutti gli assegnamenti del livello corrente
        List<AssignedLiteral> levelAssignments = decisionStack.getAssignmentsAtLevel(level);

        // Per ogni letterale della clausola
        for (Integer literal : clause) {
            Integer variable = Math.abs(literal);
            boolean expectedValue = literal > 0;

            // Cerca se c'è un'assegnazione opposta sullo stesso livello
            for (AssignedLiteral assignment : levelAssignments) {
                if (assignment.getVariable().equals(variable) &&
                        assignment.getValue() != expectedValue &&
                        assignment.hasAncestorClause()) {

                    // Trovato conflitto - ritorna la clausola ancestrale
                    return assignment.getAncestorClause();
                }
            }
        }

        return null; // Nessun conflitto trovato
    }

    /**
     * Trova il letterale asserito nella clausola (opposto alla decisione del livello corrente).
     *
     * @param clause clausola da analizzare
     * @param currentLevel livello decisionale corrente
     * @return letterale asserito, o null se non trovato
     */
    private Integer findAssertedLiteral(List<Integer> clause, int currentLevel) {
        // Ottieni la decisione del livello corrente
        List<AssignedLiteral> currentLevelAssignments = decisionStack.getAssignmentsAtLevel(currentLevel);

        for (AssignedLiteral assignment : currentLevelAssignments) {
            if (assignment.isDecision()) {
                // Trovata la decisione del livello
                Integer decisionVariable = assignment.getVariable();
                boolean decisionValue = assignment.getValue();

                // Cerca il letterale opposto nella clausola
                for (Integer literal : clause) {
                    if (Math.abs(literal) == decisionVariable) {
                        // Verifica se è opposto alla decisione
                        boolean literalPositive = literal > 0;
                        if (literalPositive != decisionValue) {
                            return literal; // Questo è il letterale asserito
                        }
                    }
                }
            }
        }

        return null; // Nessun letterale asserito trovato
    }

    /**
     * Trova il livello di backtrack per il letterale asserito.
     *
     * @param clause clausola di conflitto
     * @param assertedLiteral letterale asserito da propagare
     * @param currentLevel livello corrente
     * @return livello target per il backtrack
     */
    private int findBacktrackLevel(List<Integer> clause, Integer assertedLiteral, int currentLevel) {
        int maxLevel = -1;

        // Per ogni letterale nella clausola (eccetto l'asserito)
        for (Integer literal : clause) {
            if (!literal.equals(assertedLiteral)) {
                Integer variable = Math.abs(literal);

                // Trova il livello di assegnazione di questa variabile
                for (int level = currentLevel; level >= 0; level--) {
                    List<AssignedLiteral> levelAssignments = decisionStack.getAssignmentsAtLevel(level);

                    for (AssignedLiteral assignment : levelAssignments) {
                        if (assignment.getVariable().equals(variable)) {
                            // Trovato il livello di questa variabile
                            maxLevel = Math.max(maxLevel, level);
                            break;
                        }
                    }
                }
            }
        }

        // Il livello di backtrack è il massimo tra i livelli delle altre variabili
        // o 0 se non ci sono altre variabili assegnate
        return Math.max(0, maxLevel);
    }


    //######################################################################

    //######################################################################

    //######################################################################



    /**
     * Genera la clausola da apprendere tramite la risoluzione binaria tra due clausole.
     *
     * @param clause1 prima clausola da risolvere (può essere null)
     * @param clause2 seconda clausola da risolvere (può essere null)
     * @return clausola appresa risultante dalla risoluzione, ordinata numericamente
     */
    private List<Integer> generateExplanation(List<Integer> clause1, List<Integer> clause2) {

        Set<Integer> result = new HashSet<>();                         // Set per unione ed eliminazione duplicati

        // STEP 1: si aggiungono i letterali della prima clausola
        if (clause1 != null) result.addAll(clause1);                  // Inizializza con letterali di clause1

        // STEP 2: risoluzione con la seconda clausola
        if (clause2 != null) {
            for (Integer literal : clause2) {                         // Esamina ogni letterale di clause2
                if (result.contains(-literal)) {
                    // A e !A si annullano nella risoluzione
                    result.remove(-literal);                          // Rimuove coppia complementare
                } else {
                    // Si esegue l'unione: letterale non ha complementare => aggiunge alla clausola risultante
                    result.add(literal);                              // Aggiunge letterale al risultato
                }
            }
        }

        // STEP 3: si esegue la conversione e l'ordinamento finale
        List<Integer> explanation = new ArrayList<>(result);          // Converte Set in List per l'ordinamento
        explanation.sort(Integer::compareTo);
        return explanation;                                           // Clausola appresa pronta per l'uso
    }

    //endregion


    //region SUPPORTO CONFLICT ANALYSIS

    /**
     * Trova la clausola giustificante per avviare il processo di analisi dei conflitti.
     *
     * @param conflictClause clausola falsificata che richiede analisi del conflitto
     * @return clausola ancestrale dell'implicazione che causa il conflitto, o null se non trovata
     */
    private List<Integer> findJustifyingClauseForConflict(List<Integer> conflictClause) {

        // Recupera tutte le implicazioni in ordine cronologico di assegnamento
        List<AssignedLiteral> implications = getAllImplications();

        for (int i = implications.size() - 1; i >= 0; i--) {          // Dal più recente al più vecchio
            AssignedLiteral impl = implications.get(i);               // Implicazione corrente da esaminare

            // Verifica se questa implicazione è coinvolta nel conflitto attuale
            if (isVariableInvolvedInConflict(impl.getVariable(), impl.getValue(), conflictClause)) {
                return impl.getAncestorClause();
            }
        }

        return null;        // Fallback: nessuna clausola giustificante identificata
    }

    /**
     * Verifica se una variabile assegnata contribuisce direttamente al conflitto.
     *
     * Una variabile è coinvolta nel conflitto se:
     * 1. Appare nella clausola falsificata (quella di conflitto)
     * 2. Il suo valore assegnato rende falso il letterale corrispondente
     *
     * @param variable ID della variabile da verificare
     * @param value valore assegnato alla variabile (true/false)
     * @param conflictClause clausola falsificata da analizzare
     * @return true se la variabile contribuisce al conflitto, false altrimenti
     */
    private boolean isVariableInvolvedInConflict(Integer variable, Boolean value,
                                                 List<Integer> conflictClause) {

        // Controlla tutti i letterali della clausola falsificata
        for (Integer literal : conflictClause) {
            if (Math.abs(literal) == variable.intValue()) {

                boolean expectedPositive = literal > 0;

                return (expectedPositive && !value) || (!expectedPositive && value);
            }
        }

        // Variabile non presente nella clausola conflitto
        return false;
    }

    /**
     * Raccoglie tutte le implicazioni con clausole dall'intero decision stack.
     *
     * @return lista cronologica di tutte le implicazioni tracciabili nel decision stack
     */
    private List<AssignedLiteral> getAllImplications() {

        List<AssignedLiteral> all = new ArrayList<>();                 // Colleziona il risultato in ordine cronologico

        // Si effettua una scansione cronologica di tutti i livelli decisionali
        for (int level = 0; level < decisionStack.size(); level++) {

            // Filtra gli assegnamenti del livello corrente per trovare implicazioni valide
            decisionStack.getAssignmentsAtLevel(level).stream()
                    .filter(a -> a.isImplication() && a.hasAncestorClause())
                    .forEach(all::add);
        }

        return all;        // Storia completa implicazioni per conflict analysis
    }

    /**
     * Verifica se una clausola è consistente con gli assegnamenti correnti delle variabili.
     *
     * Stati possibili:
     * - Consistente: clausola utilizzabile per il backtrack
     * - Inconsistente: tutti letterali falsi -> serve una ulteriore risoluzione
     *
     * @param clause clausola da verificare contro gli assegnamenti correnti
     * @return true se clausola è consistente (utilizzabile), false se completamente falsificata
     */
    private boolean isConsistentWithCurrentAssignments(List<Integer> clause) {

        boolean hasUnassigned = false;
        boolean hasTrue = false;

        // Si scansionano i letterali per determinare la consistenza
        for (Integer literal : clause) {
            Integer variable = Math.abs(literal);                           // Estrae l'ID della variabile (senza segno)
            boolean expected = literal > 0;                                 // Polarità attesa: positivo=true, negativo=false
            AssignedLiteral assignment = assignedValues.get(variable);      // Recupera l'assegnamento corrente

            if (assignment == null) {
                hasUnassigned = true;                                       // Possibilità futura di soddisfacimento

            } else if (assignment.getValue() == expected) {
                hasTrue = true;                                             // Clausola già soddisfatta
                break;
            }
        }

        return hasTrue || hasUnassigned;                                    // Consistente se: vero oppure non completamente assegnata
    }

    /**
     * Trova la prossima clausola giustificante per continuare il processo di risoluzione.
     *
     * @param clause clausola inconsistente che richiede risoluzione ulteriore
     * @return clausola giustificante per continuare la risoluzione, o null se non trovata
     */
    private List<Integer> findNextJustifyingClause(List<Integer> clause) {

        // Recupera le implicazioni in ordine cronologico inverso (più recenti prima)
        List<AssignedLiteral> implications = getAllImplications();
        Collections.reverse(implications);

        for (Integer literal : clause) {
            Integer variable = Math.abs(literal);                    // Estrae l'ID variabile da risolvere

            for (AssignedLiteral impl : implications) {              // Scandisce le implicazioni (recenti -> vecchie)
                if (impl.getVariable().equals(variable) && impl.hasAncestorClause()) {
                    // Ecco trovata un'implicazione rilevante
                    return impl.getAncestorClause();                 // Restituisce la clausola che ha causato l'implicazione
                }
            }
        }

        for (Integer literal : clause) {                             // Ripete per ogni variabile se le implicazioni falliscono
            Integer variable = Math.abs(literal);                    // ID variabile da risolvere

            for (List<Integer> originalClause : formula.getClauses()) {
                // Verifica se la clausola originale contiene la variabile target
                if (originalClause.stream().anyMatch(l -> Math.abs(l) == variable.intValue())) {
                    return originalClause;                            // Restituisce prima clausola originale che contiene variabile
                }
            }
        }

        // Nessuna clausola giustificante trovata (situazione anomala)
        return null;
    }

    /**
     * Verifica la consistenza di una nuova clausola con tutte le clausole apprese precedentemente.
     *
     * @param newClause clausola da verificare contro il database delle clausole apprese
     * @return clausola conflittuale se trovata, null se la nuova clausola è consistente
     */
    private List<Integer> checkConsistencyWithLearnedClauses(List<Integer> newClause) {

        // Verifica se la clausola è unitaria
        if (newClause.size() == 1) {
            return checkUnitClauseConsistency(newClause);             // Controllo specializzato per unità
        }
        return checkNonUnitClauseConsistency(newClause);              // Controllo generale per multi-letterale
    }

    /**
     * Verifica la consistenza di una clausola unitaria contro gli assegnamenti fissi e le clausole unitarie apprese.
     *
     * @param unitClause clausola unitaria da verificare (contiene un solo letterale)
     * @return clausola conflittuale se contraddizione rilevata, null se consistente
     */
    private List<Integer> checkUnitClauseConsistency(List<Integer> unitClause) {

        // Estrae le informazioni dalla clausola unitaria
        Integer literal = unitClause.get(0);                          // Unico letterale nella clausola
        Integer variable = Math.abs(literal);                         // ID della variabile (senza segno)
        Boolean expected = literal > 0;                               // Valore richiesto: positivo=true, negativo=false

        // Si controllano i conflitti con gli assegnamenti fissi
        for (AssignedLiteral assignment : decisionStack.getAssignmentsAtLevel(0)) {
            if (assignment.getVariable().equals(variable) && !assignment.getValue().equals(expected)) {

                // Assegnamento fisso incompatibile
                return Arrays.asList(-literal);                       // Restituisce il letterale complementare come conflitto
            }
        }

        // Si controllano i conflitti con le clausole unitarie apprese
        for (List<Integer> learned : learnedClauses) {
            if (learned.size() == 1) {
                Integer learnedLiteral = learned.get(0);             // Letterale della clausola appresa
                Integer learnedVar = Math.abs(learnedLiteral);       // Variabile della clausola appresa

                if (learnedVar.equals(variable) && (learnedLiteral > 0) != expected) {

                    // Conflitto tra clausole unitarie
                    return learned;                                  // Restituisce clausola appresa conflittuale
                }
            }
        }

        // Nessun conflitto: la clausola può essere aggiunta senza problemi
        return null;
    }

    /**
     * Verifica la consistenza di una clausola multi-letterale contro tutte le clausole esistenti.
     *
     * @param clause clausola multi-letterale da verificare per consistenza
     * @return prima clausola conflittuale trovata, o null se nessun conflitto rilevato
     */
    private List<Integer> checkNonUnitClauseConsistency(List<Integer> clause) {

        // Si controllano i conflitti con le clausole originali
        for (List<Integer> existing : formula.getClauses()) {
            if (areClausesContradictory(clause, existing)) {
                return existing;                                      // Restituisce la prima clausola originale conflittuale
            }
        }

        // Si controllano i conflitti con le clausole apprese
        for (List<Integer> existing : learnedClauses) {
            if (areClausesContradictory(clause, existing)) {
                return existing;                                      // Restituisce prima clausola appresa conflittuale
            }
        }

        // Nessun conflitto: la clausola può essere aggiunta senza problemi
        return null;
    }

    /**
     * Verifica se due clausole sono logicamente contraddittorie.
     *
     * @param c1 prima clausola da confrontare
     * @param c2 seconda clausola da confrontare
     * @return true se clausole contraddittorie (risoluzione vuota), false altrimenti
     */
    private boolean areClausesContradictory(List<Integer> c1, List<Integer> c2) {
        return generateExplanation(c1, c2).isEmpty();              // Risoluzione vuota = contraddizione
    }

    /**
     * Aggiorna i contatori VSIDS per l'euristica decisionale.
     * Strategia: variabili problematiche -> maggiore priorità -> decisioni più efficaci
     *
     * @param conflictClause clausola che ha causato il conflitto corrente
     */
    private void updateVSIDSCounters(List<Integer> conflictClause) {

        // Incrementa il punteggio di ogni letterale coinvolto nel conflitto
        for (Integer literal : conflictClause) {
            vsidsCounter.merge(literal, 1, Integer::sum);
        }
    }

    //endregion


    //region LEARNING E BACKTRACKING

    /**
     * Esegue la sequenza completa di apprendimento e backtrack dopo un'analisi del conflitto.
     *
     * @param analysis risultato dell'analisi del conflitto contenente clausola appresa e livello target
     */
    private void executeLearningAndBacktrack(ConflictAnalysisResult analysis) {
        List<Integer> learnedClause = analysis.getLearnedClause();      // Clausola derivata dalla risoluzione
        int backtrackLevel = analysis.getBacktrackLevel();              // Livello decisionale target

        // Apprendimento della clausola
        if (!learnedClause.isEmpty()) {
            learnClauseIfNovel(learnedClause);                          // Aggiunge solo se non duplicata

            // Aggiorna le statistiche di apprendimento
            statistics.incrementLearnedClauses();
            updateCurrentDecisionStats(stats -> stats.learnedClauses++);
        }

        // Effettua il backtrack al livello target
        if (!learnedClause.isEmpty() || backtrackLevel > 0) {
            performBacktrack(backtrackLevel);                           // Torna al livello appropriato
        }

        // Asserzione unitaria
        if (!learnedClause.isEmpty()) {
            applyUnitAssertion(learnedClause);                          // Propaga come nuova implicazione
        }
    }

    /**
     * Aggiunge una clausola al database delle clausole apprese solo se non è duplicata.
     *
     * @param clause clausola candidata per l'apprendimento
     */
    private void learnClauseIfNovel(List<Integer> clause) {
        // Verifica l'unicità
        if (!isClauseDuplicate(clause)) {
            learnedClauses.add(new ArrayList<>(clause));                // Aggiunge copia indipendente
        }
    }

    /**
     * Verifica se una clausola è già presente in memoria (originali + apprese).
     *
     * @param clause clausola da verificare per duplicazione
     * @return true se clausola già esistente, false se nuova
     */
    private boolean isClauseDuplicate(List<Integer> clause) {
        Set<Integer> clauseSet = new HashSet<>(clause);                 // Conversione per un confronto semantico

        // Verifica i duplicati nelle clausole originali
        for (List<Integer> existing : formula.getClauses()) {
            if (new HashSet<>(existing).equals(clauseSet)) return true;
        }

        // Verifica duplicati nelle clausole apprese
        for (List<Integer> existing : learnedClauses) {
            if (new HashSet<>(existing).equals(clauseSet)) return true;
        }

        // Clausola nuova: può essere appresa
        return false;
    }

    /**
     * Esegue il backtrack non-cronologico al livello decisionale specificato.
     *
     * @param targetLevel livello decisionale dove tornare (0 = root)
     */
    private void performBacktrack(int targetLevel) {
        int current = decisionStack.getLevel();                             // Livello corrente
        if (targetLevel >= current) return;                                 // Nessun backtrack necessario

        // Rimuove i livelli dal decision stack fino al target
        while (decisionStack.getLevel() > targetLevel) {
            List<AssignedLiteral> removed = decisionStack.deleteLevel();    // Rimuove livello più alto

            // Cancella gli assegnamenti corrispondenti dalla mappa globale
            for (AssignedLiteral assignment : removed) {
                assignedValues.put(assignment.getVariable(), null);         // Marca la variabile come non assegnata
            }
        }

        statistics.incrementBackjumps();
    }

    /**
     * Applica unit assertion per clausole unitarie apprese.
     *
     * @param clause clausola appresa da applicare (dovrebbe essere unitaria)
     */
    private void applyUnitAssertion(List<Integer> clause) {

        // La clausola deve essere unitaria
        if (clause.size() == 1) {
            Integer literal = clause.get(0);                          // Unico letterale nella clausola
            Integer variable = Math.abs(literal);                     // ID della variabile
            Boolean value = literal > 0;

            if (assignedValues.get(variable) == null) {
                // Crea l'assegnamento come implicazione (non decisione)
                AssignedLiteral assertion = new AssignedLiteral(variable, value, false, clause);
                assignedValues.put(variable, assertion);                    // Registra nella mappa globale
                decisionStack.addImpliedLiteral(variable, value, clause);   // Aggiunge al decision stack
            }
        }
    }

    //endregion


    //region RESTART

    /**
     * Esegue restart completo dell'algoritmo CDCL mantenendo clausole apprese ottimizzate.
     *
     * @return risultato indicante backtrack al livello 0 per ricominciare
     */
    private ConflictAnalysisResult executeRestart() {
        try {
            // Recupera lo stato da preservare attraverso il restart
            List<AssignedLiteral> level0 = decisionStack.getAssignmentsAtLevel(0);
            RestartTechnique.RestartResult result = restartTechnique.executeRestart(level0, new ArrayList<>(learnedClauses));

            // Sequenza per il reinizio
            performRestartBacktrack();                                 // Backtrack completo al livello 0
            updateLearnedClausesFromRestart(result);                   // Aggiorna con le clausole ottimizzate
            resetAntiLoopTracking();                                   // Azzera il tracking per una nuova ricerca

            return ConflictAnalysisResult.backtrack(Collections.emptyList(), 0);    // Ricomincia da livello 0

        } catch (Exception e) {
            LOGGER.log(Level.WARNING, "Errore restart", e);
            return ConflictAnalysisResult.backtrack(Collections.emptyList(), 0);
        }
    }

    /**
     * Esegue backtrack completo al livello 0 per il reinizio.
     */
    private void performRestartBacktrack() {
        // Continua fino al livello radice
        while (decisionStack.getLevel() > 0) {
            List<AssignedLiteral> removed = decisionStack.deleteLevel();    // Rimuove il livello decisionale

            // Cancella gli assegnamenti delle variabili rimosse
            for (AssignedLiteral assignment : removed) {
                assignedValues.put(assignment.getVariable(), null);         // Marca come non assegnata
            }
        }
    }

    /**
     * Aggiorna la memoria delle clausole apprese con il set ottimizzato dal reinizio.
     *
     * @param result risultato del restart contenente clausole ottimizzate
     */
    private void updateLearnedClausesFromRestart(RestartTechnique.RestartResult result) {
        learnedClauses.clear();                                        // Rimuove tutte le clausole correnti
        learnedClauses.addAll(result.optimizedLearnedClauses);         // Sostituisce con la versione ottimizzata
    }

    /**
     * Azzeramento del tracking anti-loop per permettere nuova esplorazione dopo il reinizio.
     *
     */
    private void resetAntiLoopTracking() {
        alreadyChosenVariables.clear();                                // Azzera tracking variabili provate
    }

    //endregion

    //region FASE DI DECISIONE

    /**
     * Esegue una decisione tramite l'euristica selezionando la variabile e la polarità ottimale.
     *
     */
    private void executeDecisionMaking() {
        // Trova la miglior variabile con protezione anti-loop
        VariableSelection selection = findBestVariableWithAntiLoop();
        if (selection == null) {
            throw new IllegalStateException("Decision making: nessuna variabile disponibile");
        }

        // Registra e applica la decisione
        recordDecision(selection.variable, selection.polarity);        // Crea assegnamento decisionale
        alreadyChosenVariables.add(selection.variable);                // Aggiorna tracking anti-loop
    }

    /**
     * Trova la miglior variabile con strategia anti-loop per prevenire cicli.
     *
     * @return selezione di variabile e polarità, o null se nessuna disponibile
     */
    private VariableSelection findBestVariableWithAntiLoop() {
        // Cerca variabili mai tentate nel ciclo corrente
        VariableSelection fresh = findUntriedVariable();
        if (fresh != null) return fresh;

        // Azzera il tracking se sono state tentate tutte
        List<Integer> unassigned = getUnassignedVariables();         // Variabili ancora libere
        if (unassigned.isEmpty()) return null;

        // Azzeramento del tracking per nuovo ciclo
        alreadyChosenVariables.clear();                               // Azzera il tracking variabili provate

        return findFirstUnassignedVariable();                         // Riprova dalla prima disponibile
    }

    /**
     * Trova la prima variabile non assegnata che non è stata ancora tentata.
     *
     * @return selezione della prima variabile non tentata, o null se tutte tentate
     */
    private VariableSelection findUntriedVariable() {
        for (Map.Entry<Integer, AssignedLiteral> entry : assignedValues.entrySet()) {
            // ID variabile
            Integer var = entry.getKey();
            if (entry.getValue() == null && !alreadyChosenVariables.contains(var)) {
                // Variabile non assegnata e non ancora tentata
                return new VariableSelection(var, selectOptimalPolarity(var));      // Crea la selezione con polarità ottimale
            }
        }
        return null;                                                                // Tutte le variabili sono state tentate
    }

    /**
     * Trova la prima variabile non assegnata (fallback quando il tracking è resetato).
     *
     * @return selezione della prima variabile non assegnata, o null se tutte assegnate
     */
    private VariableSelection findFirstUnassignedVariable() {
        for (Map.Entry<Integer, AssignedLiteral> entry : assignedValues.entrySet()) {
            if (entry.getValue() == null) {
                return new VariableSelection(entry.getKey(), selectOptimalPolarity(entry.getKey()));
            }
        }
        return null;
    }

    /**
     * Ottiene la lista di tutte le variabili non ancora assegnate.
     *
     * @return lista degli ID delle variabili senza assegnamento
     */
    private List<Integer> getUnassignedVariables() {
        return assignedValues.entrySet().stream()
                .filter(e -> e.getValue() == null)          // Solo variabili non assegnate
                .map(Map.Entry::getKey)                                                // Estrae l'ID variabile
                .toList();
    }

    /**
     * Seleziona la polarità ottimale per una variabile basandosi sui contatori VSIDS.
     *
     * @param variable ID della variabile per cui determinare la polarità
     * @return true se polarità positiva preferita, false se negativa preferita
     */
    private Boolean selectOptimalPolarity(Integer variable) {
        int positive = vsidsCounter.getOrDefault(variable, 0);       // Frequenza letterale positivo
        int negative = vsidsCounter.getOrDefault(-variable, 0);      // Frequenza letterale negativo
        return positive >= negative;                                            // Si cerca di preferire la polarità più frequente nei conflitti
    }

    /**
     * Registra una decisione euristica nel decision stack e nelle statistiche.
     *
     * @param variable ID della variabile da assegnare
     * @param value valore booleano da assegnare alla variabile
     */
    private void recordDecision(Integer variable, Boolean value) {
        // Aggiorna contatori e statistiche
        decisionCount++;                                             // Contatore locale decisioni
        statistics.incrementDecisions();                             // Statistiche globali

        // Crea un record statistiche per questo livello decisionale
        DecisionStatistics stats = new DecisionStatistics(decisionCount);
        decisionStatisticsList.add(stats);                          // Aggiunge alle statistiche dettagliate

        // Crea e registra l'assegnamento decisionale
        AssignedLiteral decision = new AssignedLiteral(variable, value, true, null);

        assignedValues.put(variable, decision);                      // Registra nella mappa globale
        decisionStack.addDecision(variable, value);                  // Crea un nuovo livello decisionale
    }

    //endregion


    //region VERIFICA SODDISFACIMENTO

    /**
     * Verifica se la formula CNF è completamente soddisfatta dagli assegnamenti correnti.
     *
     * @return true se formula completamente soddisfatta, false altrimenti
     */
    private boolean isFormulaSatisfied() {
        // Verifica se tutte le variabili sono state assegnate
        if (!areAllVariablesAssigned()) return false;

        // Verifica il soddisfacimento di tutte le clausole (originali + apprese)
        return areAllClausesSatisfied(formula.getClauses()) && areAllClausesSatisfied(learnedClauses);
    }

    /**
     * Verifica se tutte le variabili della formula hanno un assegnamento definitivo.
     *
     * @return true se nessuna variabile è null, false se esistono variabili non assegnate
     */
    private boolean areAllVariablesAssigned() {
        return assignedValues.values().stream().noneMatch(Objects::isNull);
    }

    /**
     * Verifica se tutte le clausole in una collezione sono soddisfatte.
     *
     * @param clauses collezione di clausole da verificare
     * @return true se tutte soddisfatte, false se almeno una non soddisfatta
     */
    private boolean areAllClausesSatisfied(List<List<Integer>> clauses) {
        return clauses.stream().allMatch(clause ->
                evaluateClauseState(clause).getStatus() == ClauseEvaluationResult.Status.SATISFIED);
    }

    //endregion


    //region GESTIONE DEI RISULTATI

    /**
     * Gestisce l'interruzione del solver per timeout, lanciando un'eccezione appropriata.
     *
     * @return non ritorna mai, lancia sempre RuntimeException
     */
    private SATResult handleInterruption() {
        System.out.println("[I] Risoluzione interrotta per timeout");
        throw new RuntimeException("Timeout raggiunto durante la risoluzione SAT");
    }

    /**
     * Gestisce gli errori critici durante l'esecuzione CDCL con fallback appropriati.
     *
     * @param e eccezione critica che ha causato il fallimento
     * @return non ritorna mai, lancia sempre RuntimeException
     */
    private SATResult handleCriticalError(Exception e) {
        System.out.println("[E] Errore critico durante risoluzione CDCL: " + e.getMessage());

        // Verifica se è realmente un timeout
        if (interrupted || Thread.currentThread().isInterrupted()) {
            throw new RuntimeException("Timeout raggiunto durante la risoluzione SAT");
        }

        // Errore critico reale: propaga con contesto
        throw new RuntimeException("Errore critico nella risoluzione SAT: " + e.getMessage(), e);
    }

    /**
     * Genera il risultato finale dell'esecuzione CDCL con modello o prova di insoddisfacibilità.
     *
     * @param executionResult risultato dell'esecuzione contenente tipo e stato finale
     * @return SATResult completo con modello/prova e statistiche dettagliate
     */
    private SATResult generateFinalResult(CDCLExecutionResult executionResult) {
        synchronizeFinalStatistics();                                 // Allinea tutte le metriche
        logFinalStatistics();                                         // Output performance per analisi

        return switch (executionResult.getType()) {
            case SATISFIABLE -> {       // Formula soddisfacibile: genera modello completo
                Map<String, Boolean> model = generateSatisfiableModel();        // Assegnamenti variabili -> nomi
                yield SATResult.satisfiable(model, statistics);                 // Risultato con modello e statistiche
            }
            case UNSATISFIABLE -> {     // Formula insoddisfacibile: genera prova matematica
                String proof = proofGenerator.generateProof();                  // Prova di risoluzione
                statistics.setProofSize(proofGenerator.getStepCount());         // Statistiche della prova
                yield SATResult.unsatisfiable(proof, statistics);               // Risultato con prova e statistiche
            }
            case TIMEOUT -> throw new RuntimeException("Timeout raggiunto - limite iterazioni superato");
            case INTERRUPTED -> throw new RuntimeException("Solver interrotto per timeout esterno");
            default -> throw new IllegalStateException("Tipo risultato non gestito: " + executionResult.getType());
        };
    }

    /**
     * Genera il modello soddisfacente mappando variabili numeriche ai nomi originali.
     *
     * @return mappa nome_variabile -> valore_booleano per tutte le variabili
     */
    private Map<String, Boolean> generateSatisfiableModel() {
        Map<String, Boolean> model = new HashMap<>();
        Map<Integer, String> inverseMapping = createInverseVariableMapping();       // ID -> nome

        for (int variable = 1; variable <= formula.getVariableCount(); variable++) {
            AssignedLiteral assignment = assignedValues.get(variable);              // Assegnamento corrente
            String name = inverseMapping.getOrDefault(variable, String.valueOf(variable)); // Nome oppure ID

            if (assignment != null) {
                model.put(name, assignment.getValue());                             // Usa il valore assegnato
            } else {
                model.put(name, false);                                             // Default per le variabili libere
            }
        }

        return model;
    }

    //endregion


    //region STATISTICHE E LOGGING

    /**
     * Sincronizza le statistiche finali da tutte le fonti per report accurato.
     */
    private void synchronizeFinalStatistics() {
        // Aggiunge il breakdown per ciascun livello decisionale
        for (DecisionStatistics decStats : decisionStatisticsList) {
            statistics.addDecisionBreakdown(
                    decStats.decisionNumber, decStats.propagations,
                    decStats.conflicts, decStats.explanations, decStats.learnedClauses);
        }
    }

    /**
     * Registra le statistiche finali nei log per analisi delle performance.
     */
    private void logFinalStatistics() {
        System.out.println("\n\n=== STATISTICHE FINALI CDCL ===");
        System.out.println("Decisioni: " + decisionCount);                                    // Decisioni euristiche totali
        System.out.println("Conflitti: " + conflictCount);                                    // Conflitti rilevati
        System.out.println("Clausole apprese: " + learnedClauses.size());                     // Conoscenza acquisita
        System.out.println("Tempo esecuzione: " + statistics.getExecutionTimeMs() + " ms");   // Performance temporale

        if (restartTechnique != null) {
            System.out.println("[I] Restart: " + restartTechnique.getTotalRestarts());        // Restart eseguiti
        }
    }

    /**
     * Aggiorna le statistiche del livello decisionale corrente.
     *
     * @param updater funzione che modifica le statistiche del livello corrente
     */
    private void updateCurrentDecisionStats(java.util.function.Consumer<DecisionStatistics> updater) {
        if (!decisionStatisticsList.isEmpty()) {
            updater.accept(decisionStatisticsList.get(decisionStatisticsList.size() - 1));
        }
    }

    /**
     * Verifica se il thread è stato interrotto e lancia l'eccezione appropriata.
     *
     * @throws InterruptedException se interruzione rilevata
     */
    private void checkForInterruption() throws InterruptedException {
        if (Thread.currentThread().isInterrupted() || interrupted) {
            throw new InterruptedException("Solver interrotto per timeout");
        }
    }

    /**
     * Registra informazioni di progresso durante l'esecuzione per monitoring.
     *
     * @param iterations numero di iterazioni del loop principale CDCL
     */
    private void logProgress(int iterations) {
        int assigned = (int) assignedValues.values().stream().filter(Objects::nonNull).count();     // Variabili assegnate
        int total = formula.getVariableCount();                                                     // Variabili totali
        int level = decisionStack.getLevel();                                                       // Livello decisionale corrente

        System.out.printf("Iterazione %d - Livello: %d, Decisioni: %d, Conflitti: %d, Assegnate: %d/%d\n",
                iterations, level, decisionCount, conflictCount, assigned, total);
    }

    //endregion

    //region CLASSI DI SUPPORTO

    /**
     * Rappresenta la selezione di una variabile con la sua polarità ottimale.
     *
     */
    private static class VariableSelection {
        final Integer variable;             // ID della variabile selezionata
        final Boolean polarity;             // Polarità ottimale (true=positiva, false=negativa)

        VariableSelection(Integer variable, Boolean polarity) {
            this.variable = variable;
            this.polarity = polarity;
        }
    }

    /**
     * Rappresenta il risultato finale dell'esecuzione dell'algoritmo CDCL.
     *
     */
    private static class CDCLExecutionResult {
        public enum Type {
            SATISFIABLE,        // Formula soddisfacibile: modello trovato
            UNSATISFIABLE,      // Formula insoddisfacibile: prova derivata
            TIMEOUT,            // Limite iterazioni raggiunto
            INTERRUPTED         // Interruzione esterna (timeout utente)
        }

        private final Type type;

        private CDCLExecutionResult(Type type) { this.type = type; }

        public Type getType() { return type; }

        // Factory methods per creazione type-safe
        public static CDCLExecutionResult satisfiable() { return new CDCLExecutionResult(Type.SATISFIABLE); }
        public static CDCLExecutionResult unsatisfiable() { return new CDCLExecutionResult(Type.UNSATISFIABLE); }
        public static CDCLExecutionResult timeout() { return new CDCLExecutionResult(Type.TIMEOUT); }
        public static CDCLExecutionResult interrupted() { return new CDCLExecutionResult(Type.INTERRUPTED); }
    }

    /**
     * Rappresenta il risultato dell'unit propagation.
     */
    private static class PropagationResult {
        private final boolean hasConflict;                          // Flag: conflitto rilevato
        private final List<Integer> conflictClause;                 // Clausola che ha causato il conflitto
        private final List<Integer> justifyingClause;               // Clausola giustificante per analysis

        private PropagationResult(boolean hasConflict, List<Integer> conflictClause, List<Integer> justifyingClause) {
            this.hasConflict = hasConflict;
            this.conflictClause = conflictClause;
            this.justifyingClause = justifyingClause;
        }

        public boolean hasConflict() { return hasConflict; }
        public List<Integer> getConflictClause() { return conflictClause; }
        public List<Integer> getJustifyingClause() { return justifyingClause; }

        // Factory methods per creazione type-safe
        public static PropagationResult success() {
            return new PropagationResult(false, null, null);        // Propagazione completata senza conflitti
        }

        public static PropagationResult conflict(List<Integer> conflictClause, List<Integer> justifyingClause) {
            return new PropagationResult(true, conflictClause, justifyingClause); // Conflitto con info per analysis
        }
    }

    /**
     * Rappresenta il risultato della valutazione di una clausola.
     *
     */
    private static class ClauseEvaluationResult {
        public enum Status {
            SATISFIED,        // Clausola soddisfatta: almeno un letterale vero
            FALSIFIED,        // Clausola falsificata: tutti letterali falsi → conflitto
            UNIT,             // Clausola unitaria: un solo letterale non assegnato → propagazione
            UNRESOLVED        // Clausola non risolta: più letterali non assegnati → nessuna azione
        }

        private final Status status;                                // Stato della clausola
        private final Integer unitLiteral;                          // Letterale per unit propagation (se UNIT)

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
            return new ClauseEvaluationResult(Status.UNIT, literal); // Include letterale per propagazione
        }

        public static ClauseEvaluationResult unresolved() {
            return new ClauseEvaluationResult(Status.UNRESOLVED, null);
        }
    }

    /**
     * Rappresenta il risultato dell'analisi di un conflitto.
     *
     */
    private static class ConflictAnalysisResult {
        private final boolean unsatisfiable;                        // Flag: formula UNSAT
        private final List<Integer> learnedClause;                  // Clausola appresa dalla risoluzione
        private final int backtrackLevel;                           // Livello decisionale target per backtrack

        private ConflictAnalysisResult(boolean unsatisfiable, List<Integer> learnedClause, int backtrackLevel) {
            this.unsatisfiable = unsatisfiable;
            this.learnedClause = learnedClause;
            this.backtrackLevel = backtrackLevel;
        }

        public boolean isUnsatisfiable() { return unsatisfiable; }
        public List<Integer> getLearnedClause() { return learnedClause; }
        public int getBacktrackLevel() { return backtrackLevel; }

        public static ConflictAnalysisResult unsatisfiable() {
            return new ConflictAnalysisResult(true, Collections.emptyList(), -1); // UNSAT: nessun backtrack
        }

        public static ConflictAnalysisResult backtrack(List<Integer> learnedClause, int level) {
            return new ConflictAnalysisResult(false, learnedClause, level); // Backtrack con clausola appresa
        }
    }

    //endregion
}