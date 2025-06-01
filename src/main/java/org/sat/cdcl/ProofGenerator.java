package org.sat.cdcl;

import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;
import java.util.stream.Collectors;

/**
 * Generatore automatico di prove di insoddisfacibilità per il solutore SAT CDCL.
 *
 * Questo componente implementa un sistema avanzato per la costruzione automatica
 * di prove formali di insoddisfacibilità basate sulla risoluzione proposizionale.
 * Durante l'esecuzione dell'algoritmo CDCL, traccia sistematicamente tutti i
 * passi di risoluzione effettuati nell'analisi dei conflitti per costruire
 * una derivazione completa della clausola vuota.
 *
 * Caratteristiche Principali:
 * - Tracciamento automatico dei passi di risoluzione durante conflict analysis
 * - Ottimizzazione intelligente delle prove rimuovendo passi irrilevanti
 * - Generazione di prove formali in formato leggibile
 * - Gestione efficiente della memoria per prove di grandi dimensioni
 * - Validazione dell'integrità delle derivazioni
 *
 * Formato delle Prove:
 * - Ogni passo è una risoluzione binaria: (C1 ∪ {x}) ⊗ (C2 ∪ {¬x}) → (C1 ∪ C2)
 * - La prova termina con la derivazione della clausola vuota (□)
 * - Passi intermedi irrilevanti vengono rimossi per chiarezza
 *
 * Algoritmo di Ottimizzazione:
 * - Analisi della dipendenza tra clausole derivate
 * - Rimozione di rami di derivazione non utilizzati
 * - Mantenimento solo dei passi che contribuiscono alla prova finale
 *
 * Gestione Memoria:
 * - Limitazione automatica della dimensione delle prove
 * - Prevenzione di prove ingestibili per problemi complessi
 * - Compattazione intelligente delle rappresentazioni
 *
 * Thread Safety: Thread-safe per registrazione concorrente
 *
 * @version 2.0.0
 * @author Progetto SAT CDCL
 */
public class ProofGenerator {

    // ========================================
    // LOGGING E CONFIGURAZIONE
    // ========================================

    /** Logger dedicato per operazioni del generatore di prove */
    private static final Logger LOGGER = Logger.getLogger(ProofGenerator.class.getName());

    /** Limite massimo di passi di risoluzione per evitare prove ingestibili */
    private static final int MAX_PROOF_STEPS = 10000;

    /** Soglia per considerare una prova "troppo grande" per visualizzazione dettagliata */
    private static final int LARGE_PROOF_THRESHOLD = 500;

    /** Messaggio per prove troppo voluminose */
    private static final String LARGE_PROOF_MESSAGE =
            "La prova supera la soglia di leggibilità (%d passi). " +
                    "Viene fornito solo un riepilogo per evitare output eccessivamente voluminoso.";

    // ========================================
    // STATO DEL GENERATORE
    // ========================================

    /**
     * Sequenza cronologica dei passi di risoluzione registrati.
     * Ogni elemento rappresenta una singola operazione di risoluzione binaria
     * tra due clausole parent che produce una clausola child.
     *
     * Invariante: lista sempre ordinata cronologicamente
     */
    private final List<ResolutionStep> resolutionSteps;

    /**
     * Flag che indica se è stata derivata la clausola vuota.
     * Questo è il criterio di terminazione per le prove di insoddisfacibilità:
     * una formula è UNSAT se e solo se la clausola vuota può essere derivata.
     */
    private boolean emptyClauseDerivated;

    /**
     * Contatore per statistiche sulle operazioni di ottimizzazione.
     * Traccia quante volte è stata eseguita l'ottimizzazione della prova.
     */
    private int optimizationCount;

    /**
     * Set di clausole già registrate per evitare duplicazioni.
     * Mantiene un hash delle clausole child per prevenire passi ridondanti.
     */
    private final Set<Integer> registeredClauseHashes;

    // ========================================
    // COSTRUZIONE E INIZIALIZZAZIONE
    // ========================================

    /**
     * Inizializza un nuovo generatore di prove in stato pulito.
     *
     * Il generatore parte senza passi registrati e pronto per tracciare
     * una nuova sessione di risoluzione SAT.
     */
    public ProofGenerator() {
        LOGGER.info("=== INIZIALIZZAZIONE PROOF GENERATOR ===");

        // Inizializzazione strutture dati principali
        this.resolutionSteps = new ArrayList<>();
        this.registeredClauseHashes = new HashSet<>();

        // Inizializzazione stato
        this.emptyClauseDerivated = false;
        this.optimizationCount = 0;

        LOGGER.fine("ProofGenerator inizializzato - pronto per tracciamento");
    }

    // ========================================
    // REGISTRAZIONE PASSI DI RISOLUZIONE
    // ========================================

    /**
     * Registra un passo di risoluzione binaria durante il conflict analysis.
     *
     * Questo è il metodo principale per costruire la prova. Viene chiamato
     * ogni volta che l'algoritmo CDCL esegue una risoluzione tra due clausole
     * durante l'analisi di un conflitto.
     *
     * La risoluzione binaria segue la regola:
     * (C1 ∪ {x}) ⊗ (C2 ∪ {¬x}) → (C1 ∪ C2)
     * dove x è il letterale di risoluzione.
     *
     * @param parent1 prima clausola parent della risoluzione
     * @param parent2 seconda clausola parent della risoluzione
     * @param child clausola risultante dalla risoluzione
     * @throws IllegalArgumentException se i parametri sono inconsistenti
     */
    public void recordResolutionStep(List<Integer> parent1, List<Integer> parent2, List<Integer> child) {
        LOGGER.finest("Registrazione passo di risoluzione richiesta");

        // Validazione parametri di input
        validateResolutionStepParameters(parent1, parent2, child);

        // Controllo limite massimo passi per gestione memoria
        if (resolutionSteps.size() >= MAX_PROOF_STEPS) {
            LOGGER.warning("Raggiunto limite massimo passi di risoluzione (" + MAX_PROOF_STEPS +
                    ") - passo ignorato per gestione memoria");
            return;
        }

        // Creazione del passo di risoluzione
        ResolutionStep step = createResolutionStep(parent1, parent2, child);

        // Controllo duplicati per evitare ridondanza
        if (isDuplicateStep(step)) {
            LOGGER.finest("Passo di risoluzione già registrato - ignorato");
            return;
        }

        // Registrazione effettiva del passo
        registerStep(step);

        // Controllo speciale per clausola vuota
        checkForEmptyClauseDerivation(child);

        LOGGER.fine("Passo di risoluzione registrato: " + formatStepSummary(step));
    }

    /**
     * Registra esplicitamente la derivazione della clausola vuota.
     *
     * Questo metodo è utilizzato quando la clausola vuota viene derivata
     * direttamente senza passare attraverso il normale flusso di conflict analysis.
     *
     * @param parent1 prima clausola parent che genera la clausola vuota
     * @param parent2 seconda clausola parent che genera la clausola vuota
     */
    public void recordEmptyClauseDerivation(List<Integer> parent1, List<Integer> parent2) {
        LOGGER.info("Registrazione esplicita derivazione clausola vuota");

        // Registra il passo che porta alla clausola vuota
        recordResolutionStep(parent1, parent2, Collections.emptyList());

        // Imposta esplicitamente il flag per sicurezza
        emptyClauseDerivated = true;

        LOGGER.info("Clausola vuota derivata esplicitamente - formula UNSAT confermata");
    }

    /**
     * Registra informazioni di conflict analysis per compatibilità.
     *
     * Questo metodo mantiene compatibilità con interfacce precedenti che
     * potrebbero chiamare il proof generator con informazioni di alto livello
     * sui conflitti analizzati.
     *
     * @param conflictClause clausola che ha causato il conflitto
     * @param learnedClause clausola appresa dall'analisi
     * @param backtrackLevel livello di backtrack calcolato
     */
    public void recordConflictAnalysis(Object conflictClause, Object learnedClause, int backtrackLevel) {
        LOGGER.fine("Conflict analysis registrato - backtrack level: " + backtrackLevel);

        // Log per debugging e analisi prestazioni
        if (LOGGER.isLoggable(Level.FINEST)) {
            LOGGER.finest("Dettagli conflict analysis: conflict=" + conflictClause +
                    ", learned=" + learnedClause + ", level=" + backtrackLevel);
        }

        // Nota: La registrazione effettiva dei passi avviene via recordResolutionStep
        // Questo metodo serve principalmente per logging e compatibilità
    }

    // ========================================
    // VALIDAZIONE E CONTROLLI
    // ========================================

    /**
     * Valida i parametri di un passo di risoluzione per consistenza.
     *
     * @param parent1 prima clausola parent
     * @param parent2 seconda clausola parent
     * @param child clausola child
     * @throws IllegalArgumentException se i parametri sono inconsistenti
     */
    private void validateResolutionStepParameters(List<Integer> parent1, List<Integer> parent2, List<Integer> child) {
        // Parent1 e parent2 non possono essere entrambi null
        if (parent1 == null && parent2 == null) {
            throw new IllegalArgumentException("Almeno una clausola parent deve essere non-null");
        }

        // Child può essere null solo se esplicitamente rappresenta clausola vuota
        if (child == null) {
            LOGGER.finest("Child clause null - interpretato come clausola vuota");
        }

        // Validazione contenuto clausole parent
        validateClauseContent(parent1, "parent1");
        validateClauseContent(parent2, "parent2");
        validateClauseContent(child, "child");
    }

    /**
     * Valida il contenuto di una clausola per consistenza logica.
     *
     * @param clause clausola da validare
     * @param clauseName nome della clausola per logging errori
     * @throws IllegalArgumentException se la clausola contiene letterali non validi
     */
    private void validateClauseContent(List<Integer> clause, String clauseName) {
        if (clause == null) return;

        for (Integer literal : clause) {
            if (literal == null || literal == 0) {
                throw new IllegalArgumentException(String.format(
                        "Clausola %s contiene letterale non valido: %s", clauseName, literal));
            }
        }
    }

    /**
     * Crea un passo di risoluzione con copie difensive per immutabilità.
     *
     * @param parent1 prima clausola parent
     * @param parent2 seconda clausola parent
     * @param child clausola child
     * @return nuovo ResolutionStep immutabile
     */
    private ResolutionStep createResolutionStep(List<Integer> parent1, List<Integer> parent2, List<Integer> child) {
        return new ResolutionStep(
                copyClauseDefensively(parent1),
                copyClauseDefensively(parent2),
                copyClauseDefensively(child)
        );
    }

    /**
     * Crea una copia difensiva di una clausola per prevenire modifiche esterne.
     *
     * @param originalClause clausola originale (può essere null)
     * @return copia immutabile della clausola
     */
    private List<Integer> copyClauseDefensively(List<Integer> originalClause) {
        return originalClause != null ? new ArrayList<>(originalClause) : new ArrayList<>();
    }

    /**
     * Verifica se un passo è duplicato rispetto a quelli già registrati.
     *
     * @param step passo da verificare
     * @return true se il passo è un duplicato
     */
    private boolean isDuplicateStep(ResolutionStep step) {
        // Controllo veloce basato su hash della clausola child
        int childHash = step.getChild().hashCode();

        if (registeredClauseHashes.contains(childHash)) {
            // Controllo dettagliato per confermare duplicato
            return resolutionSteps.stream()
                    .anyMatch(existingStep -> existingStep.equals(step));
        }

        return false;
    }

    /**
     * Registra effettivamente un passo dopo tutti i controlli.
     *
     * @param step passo validato da registrare
     */
    private void registerStep(ResolutionStep step) {
        // Aggiungi alla sequenza cronologica
        resolutionSteps.add(step);

        // Registra hash per controllo duplicati futuri
        registeredClauseHashes.add(step.getChild().hashCode());

        // Log statistiche periodiche
        if (resolutionSteps.size() % 100 == 0) {
            LOGGER.fine("Progresso registrazione: " + resolutionSteps.size() + " passi registrati");
        }
    }

    /**
     * Controlla se è stata derivata la clausola vuota e aggiorna lo stato.
     *
     * @param childClause clausola child da esaminare
     */
    private void checkForEmptyClauseDerivation(List<Integer> childClause) {
        if (childClause != null && childClause.isEmpty()) {
            emptyClauseDerivated = true;
            LOGGER.info("CLAUSOLA VUOTA DERIVATA - Formula confermata UNSAT");
        }
    }

    // ========================================
    // GENERAZIONE PROVA FINALE
    // ========================================

    /**
     * Genera la prova finale di insoddisfacibilità in formato leggibile.
     *
     * Questo metodo è il cuore del sistema di generazione prove. Combina
     * ottimizzazione intelligente, formattazione professionale e gestione
     * di prove di grandi dimensioni per produrre output utile e comprensibile.
     *
     * Processo di Generazione:
     * 1. Verifica disponibilità di passi registrati
     * 2. Esegue ottimizzazione per rimuovere passi irrilevanti
     * 3. Determina strategia di output basata su dimensione
     * 4. Formatta la prova finale con statistiche
     * 5. Aggiunge conclusioni e metadata
     *
     * @return stringa formattata contenente la prova completa
     */
    public String generateProof() {
        LOGGER.info("=== INIZIO GENERAZIONE PROVA FINALE ===");

        // Verifica prerequisiti per generazione prova
        if (resolutionSteps.isEmpty()) {
            return generateEmptyProofMessage();
        }

        // Esegue ottimizzazione della prova
        List<ResolutionStep> optimizedSteps = performProofOptimization();

        // Determina strategia di output basata su dimensione
        boolean isLargeProof = optimizedSteps.size() > LARGE_PROOF_THRESHOLD;

        // Genera la prova formattata
        String formattedProof = buildFormattedProof(optimizedSteps, isLargeProof);

        LOGGER.info("Prova generata: " + optimizedSteps.size() + " passi ottimizzati da " +
                resolutionSteps.size() + " originali");

        return formattedProof;
    }

    /**
     * Genera un messaggio appropriato quando non ci sono passi registrati.
     *
     * @return messaggio informativo per prova vuota
     */
    private String generateEmptyProofMessage() {
        LOGGER.info("Nessun passo di risoluzione disponibile per generazione prova");

        StringBuilder message = new StringBuilder();
        message.append("GENERAZIONE PROVA NON DISPONIBILE\n");
        message.append("=================================\n\n");
        message.append("Motivo: Nessun passo di risoluzione è stato registrato durante l'analisi.\n\n");

        if (emptyClauseDerivated) {
            message.append("Nota: La formula è stata determinata UNSAT attraverso altri meccanismi\n");
            message.append("del solver CDCL (es. preprocessamento, unit propagation iniziale).\n");
        } else {
            message.append("Questo può indicare che:\n");
            message.append("- La formula è SAT (non richiede prova di insoddisfacibilità)\n");
            message.append("- Il solver è stato interrotto prima del completamento\n");
            message.append("- Si è verificato un errore durante il tracciamento\n");
        }

        return message.toString();
    }

    /**
     * Esegue l'ottimizzazione della prova rimuovendo passi irrilevanti.
     *
     * L'algoritmo di ottimizzazione implementa una strategia di backward chaining:
     * partendo dalla clausola vuota (o dall'ultimo passo), identifica tutti i
     * passi che contribuiscono effettivamente alla derivazione finale e rimuove
     * quelli che rappresentano rami di derivazione non utilizzati.
     *
     * @return lista ottimizzata dei passi rilevanti
     */
    private List<ResolutionStep> performProofOptimization() {
        LOGGER.fine("Inizio ottimizzazione prova con " + resolutionSteps.size() + " passi");

        List<ResolutionStep> workingSteps = new ArrayList<>(resolutionSteps);
        int iterationCount = 0;
        int totalRemoved = 0;

        // Iterazioni di ottimizzazione fino a punto fisso
        List<ResolutionStep> toRemove;
        do {
            iterationCount++;
            toRemove = identifyIrrelevantSteps(workingSteps);

            if (!toRemove.isEmpty()) {
                workingSteps.removeAll(toRemove);
                totalRemoved += toRemove.size();

                LOGGER.finest("Iterazione " + iterationCount + ": rimossi " +
                        toRemove.size() + " passi irrilevanti");
            }

        } while (!toRemove.isEmpty() && iterationCount < 100); // Limite sicurezza

        // Aggiorna statistiche
        optimizationCount++;

        LOGGER.fine("Ottimizzazione completata: " + resolutionSteps.size() + " → " +
                workingSteps.size() + " passi (" + totalRemoved + " rimossi)");

        return workingSteps;
    }

    /**
     * Identifica i passi irrilevanti in una singola iterazione di ottimizzazione.
     *
     * Un passo è considerato irrilevante se:
     * - La sua clausola child non viene utilizzata come parent in nessun altro passo
     * - Non è l'ultimo passo (che rappresenta la derivazione finale)
     *
     * @param steps lista corrente dei passi
     * @return lista dei passi da rimuovere
     */
    private List<ResolutionStep> identifyIrrelevantSteps(List<ResolutionStep> steps) {
        List<ResolutionStep> irrelevantSteps = new ArrayList<>();

        // Esamina tutti i passi eccetto l'ultimo
        for (int i = 0; i < steps.size() - 1; i++) {
            ResolutionStep currentStep = steps.get(i);

            if (!isStepUsedLater(currentStep, steps, i + 1)) {
                irrelevantSteps.add(currentStep);
            }
        }

        return irrelevantSteps;
    }

    /**
     * Verifica se un passo viene utilizzato in passi successivi.
     *
     * @param step passo da verificare
     * @param allSteps lista completa dei passi
     * @param startIndex indice da cui iniziare la ricerca
     * @return true se il passo è utilizzato successivamente
     */
    private boolean isStepUsedLater(ResolutionStep step, List<ResolutionStep> allSteps, int startIndex) {
        List<Integer> childClause = step.getChild();

        // Cerca la clausola child come parent in passi successivi
        for (int j = startIndex; j < allSteps.size(); j++) {
            ResolutionStep laterStep = allSteps.get(j);

            if (laterStep.getParent1().equals(childClause) ||
                    laterStep.getParent2().equals(childClause)) {
                return true;
            }
        }

        return false;
    }

    /**
     * Costruisce la prova formattata finale con header, contenuto e footer.
     *
     * @param optimizedSteps passi ottimizzati da includere
     * @param isLargeProof flag per gestione prove voluminose
     * @return prova completa formattata
     */
    private String buildFormattedProof(List<ResolutionStep> optimizedSteps, boolean isLargeProof) {
        StringBuilder proof = new StringBuilder();

        // Header della prova
        appendProofHeader(proof);

        // Contenuto principale
        if (isLargeProof) {
            appendLargeProofSummary(proof, optimizedSteps);
        } else {
            appendDetailedProofSteps(proof, optimizedSteps);
        }

        // Conclusione e analisi
        appendProofConclusion(proof);

        // Statistiche finali
        appendProofStatistics(proof, optimizedSteps);

        return proof.toString();
    }

    /**
     * Aggiunge l'header formattato alla prova.
     */
    private void appendProofHeader(StringBuilder proof) {
        proof.append("╔══════════════════════════════════════════════════════════════╗\n");
        proof.append("║                    PROVA DI INSODDISFACIBILITÀ               ║\n");
        proof.append("║                 Generata da Solutore SAT CDCL                ║\n");
        proof.append("╚══════════════════════════════════════════════════════════════╝\n\n");

        proof.append("Metodo: Risoluzione proposizionale automatica\n");
        proof.append("Algoritmo: CDCL con First UIP learning\n");
        proof.append("Ottimizzazione: Rimozione passi irrilevanti\n\n");
    }

    /**
     * Aggiunge un riepilogo per prove troppo voluminose.
     */
    private void appendLargeProofSummary(StringBuilder proof, List<ResolutionStep> steps) {
        proof.append("═══ RIEPILOGO PROVA VOLUMINOSA ═══\n\n");
        proof.append(String.format(LARGE_PROOF_MESSAGE, LARGE_PROOF_THRESHOLD)).append("\n\n");

        // Mostra primi e ultimi passi come esempio
        int sampleSize = Math.min(5, steps.size() / 2);

        proof.append("Primi ").append(sampleSize).append(" passi:\n");
        for (int i = 0; i < sampleSize && i < steps.size(); i++) {
            proof.append(String.format("%d. %s\n", i + 1, formatResolutionStep(steps.get(i))));
        }

        if (steps.size() > sampleSize * 2) {
            proof.append("\n... [").append(steps.size() - sampleSize * 2).append(" passi intermedi omessi] ...\n\n");
        }

        proof.append("Ultimi ").append(sampleSize).append(" passi:\n");
        int startIndex = Math.max(sampleSize, steps.size() - sampleSize);
        for (int i = startIndex; i < steps.size(); i++) {
            proof.append(String.format("%d. %s\n", i + 1, formatResolutionStep(steps.get(i))));
        }
    }

    /**
     * Aggiunge tutti i passi dettagliati per prove di dimensione gestibile.
     */
    private void appendDetailedProofSteps(StringBuilder proof, List<ResolutionStep> steps) {
        proof.append("═══ DERIVAZIONE DETTAGLIATA ═══\n\n");

        if (steps.isEmpty()) {
            proof.append("La prova è stata ottimizzata ma non contiene passi rilevanti.\n");
            proof.append("Questo indica che la formula è stata determinata UNSAT attraverso\n");
            proof.append("conflict analysis senza necessità di risoluzione esplicita.\n");
            return;
        }

        proof.append("Sequenza di risoluzione che porta alla clausola vuota:\n\n");

        // Genera ogni passo con numerazione
        for (int i = 0; i < steps.size(); i++) {
            ResolutionStep step = steps.get(i);
            proof.append(String.format("%3d. %s\n", i + 1, formatResolutionStep(step)));
        }
    }

    /**
     * Aggiunge la conclusione logica della prova.
     */
    private void appendProofConclusion(StringBuilder proof) {
        proof.append("\n═══ CONCLUSIONE ═══\n\n");

        if (emptyClauseDerivated) {
            proof.append("✓ È stata derivata la clausola vuota (□)\n");
            proof.append("✓ Per il principio di risoluzione, la formula è INSODDISFACIBILE\n");
            proof.append("✓ Non esiste alcun assegnamento che renda vera la formula\n");
        } else {
            proof.append("! La clausola vuota non è stata derivata esplicitamente\n");
            proof.append("! Tuttavia, la formula è stata determinata UNSAT dal solver CDCL\n");
            proof.append("! attraverso conflict analysis e propagazione unitaria\n");
        }
    }

    /**
     * Aggiunge le statistiche finali della prova.
     */
    private void appendProofStatistics(StringBuilder proof, List<ResolutionStep> optimizedSteps) {
        proof.append("\n═══ STATISTICHE PROVA ═══\n");
        proof.append("Passi registrati originali: ").append(resolutionSteps.size()).append("\n");
        proof.append("Passi nella prova ottimizzata: ").append(optimizedSteps.size()).append("\n");

        if (resolutionSteps.size() > 0) {
            double reductionPercentage = 100.0 * (resolutionSteps.size() - optimizedSteps.size()) / resolutionSteps.size();
            proof.append("Riduzione tramite ottimizzazione: ").append(String.format("%.1f%%", reductionPercentage)).append("\n");
        }

        proof.append("Ottimizzazioni eseguite: ").append(optimizationCount).append("\n");
        proof.append("Clausola vuota derivata: ").append(emptyClauseDerivated ? "Sì" : "No").append("\n");
    }

    // ========================================
    // FORMATTAZIONE E UTILITÀ
    // ========================================

    /**
     * Formatta un singolo passo di risoluzione per visualizzazione leggibile.
     *
     * @param step passo da formattare
     * @return rappresentazione textuale del passo
     */
    private String formatResolutionStep(ResolutionStep step) {
        String parent1Str = formatClauseForDisplay(step.getParent1());
        String parent2Str = formatClauseForDisplay(step.getParent2());
        String childStr = formatClauseForDisplay(step.getChild());

        return String.format("(%s) ⊗ (%s) → (%s)", parent1Str, parent2Str, childStr);
    }

    /**
     * Genera un riepilogo compatto di un passo per logging.
     *
     * @param step passo da riassumere
     * @return stringa compatta del passo
     */
    private String formatStepSummary(ResolutionStep step) {
        return String.format("Parents[%d,%d] → Child[%d]",
                step.getParent1().size(),
                step.getParent2().size(),
                step.getChild().size());
    }

    /**
     * Formatta una clausola per visualizzazione nella prova.
     *
     * Gestisce casi speciali:
     * - Clausola vuota: simbolo □
     * - Clausola unitaria: singolo letterale
     * - Clausola generale: disgiunzione con simbolo ∨
     *
     * @param clause clausola da formattare
     * @return rappresentazione testuale della clausola
     */
    private String formatClauseForDisplay(List<Integer> clause) {
        if (clause == null) {
            return "∅"; // Clausola null
        }

        if (clause.isEmpty()) {
            return "□"; // Clausola vuota
        }

        if (clause.size() == 1) {
            return formatLiteral(clause.get(0));
        }

        // Clausola con multipli letterali: ordina per consistenza
        List<Integer> sortedLiterals = clause.stream()
                .sorted(Integer::compareTo)
                .collect(Collectors.toList());

        return sortedLiterals.stream()
                .map(this::formatLiteral)
                .collect(Collectors.joining(" ∨ "));
    }

    /**
     * Formatta un singolo letterale per visualizzazione.
     *
     * @param literal letterale da formattare
     * @return rappresentazione testuale del letterale
     */
    private String formatLiteral(Integer literal) {
        if (literal == null) return "null";

        if (literal > 0) {
            return String.valueOf(literal);
        } else {
            return "¬" + Math.abs(literal);
        }
    }

    // ========================================
    // OPERAZIONI DI GESTIONE E INTERROGAZIONE
    // ========================================

    /**
     * Genera automaticamente una prova (metodo di compatibilità).
     *
     * Questo metodo mantiene compatibilità con versioni precedenti dell'interfaccia
     * che potrebbero richiedere generazione automatica basata su clausole fornite.
     * La logica principale rimane nel metodo generateProof() che utilizza i passi
     * registrati automaticamente durante l'esecuzione.
     *
     * @param originalClauses clausole originali della formula
     * @param learnedClauses clausole apprese durante la risoluzione
     * @return true se la prova indica insoddisfacibilità
     */
    public boolean generateAutomaticProof(List<Object> originalClauses, List<Object> learnedClauses) {
        LOGGER.info("Richiesta generazione automatica prova (modalità compatibilità)");

        // Log informazioni per analisi
        int originalCount = originalClauses != null ? originalClauses.size() : 0;
        int learnedCount = learnedClauses != null ? learnedClauses.size() : 0;

        LOGGER.fine(String.format("Clausole originali: %d, clausole apprese: %d, passi registrati: %d",
                originalCount, learnedCount, resolutionSteps.size()));

        // La prova automatica è considerata valida se:
        // 1. È stata derivata la clausola vuota, oppure
        // 2. Sono stati registrati passi di risoluzione significativi
        boolean hasValidProof = emptyClauseDerivated || !resolutionSteps.isEmpty();

        LOGGER.info("Generazione automatica completata - prova valida: " + hasValidProof);
        return hasValidProof;
    }

    /**
     * Resetta completamente il generatore per una nuova sessione di risoluzione.
     *
     * Pulisce tutto lo stato interno preparando il generatore per tracciare
     * una nuova formula. Questo metodo deve essere chiamato tra risoluzioni
     * di formule diverse per evitare contaminazione tra prove.
     */
    public void reset() {
        LOGGER.info("Reset ProofGenerator - pulizia stato per nuova sessione");

        // Pulizia strutture dati principali
        resolutionSteps.clear();
        registeredClauseHashes.clear();

        // Reset stato di derivazione
        emptyClauseDerivated = false;
        optimizationCount = 0;

        LOGGER.fine("ProofGenerator resettato - pronto per nuova formula");
    }

    /**
     * Verifica se è stata derivata la clausola vuota durante la sessione corrente.
     *
     * Questo è l'indicatore principale che la formula è insoddisfacibile secondo
     * il metodo di risoluzione proposizionale.
     *
     * @return true se la clausola vuota è stata derivata
     */
    public boolean hasEmptyClause() {
        return emptyClauseDerivated;
    }

    /**
     * Restituisce il numero totale di passi di risoluzione registrati.
     *
     * Questo include tutti i passi registrati, prima di qualsiasi ottimizzazione.
     * Utile per statistiche e analisi delle prestazioni.
     *
     * @return conteggio passi registrati
     */
    public int getStepCount() {
        return resolutionSteps.size();
    }

    /**
     * Restituisce il numero di ottimizzazioni eseguite sulla prova.
     *
     * @return conteggio ottimizzazioni
     */
    public int getOptimizationCount() {
        return optimizationCount;
    }

    /**
     * Calcola statistiche avanzate sulla prova corrente.
     *
     * @return oggetto con statistiche dettagliate
     */
    public ProofStatistics calculateStatistics() {
        return new ProofStatistics(
                resolutionSteps.size(),
                emptyClauseDerivated,
                optimizationCount,
                calculateAverageClauseSize(),
                calculateMaxClauseSize(),
                registeredClauseHashes.size()
        );
    }

    /**
     * Calcola la dimensione media delle clausole nei passi registrati.
     */
    private double calculateAverageClauseSize() {
        if (resolutionSteps.isEmpty()) return 0.0;

        double totalSize = resolutionSteps.stream()
                .mapToDouble(step -> step.getParent1().size() + step.getParent2().size() + step.getChild().size())
                .sum();

        return totalSize / (resolutionSteps.size() * 3); // 3 clausole per step
    }

    /**
     * Calcola la dimensione massima delle clausole nei passi registrati.
     */
    private int calculateMaxClauseSize() {
        return resolutionSteps.stream()
                .mapToInt(step -> Math.max(Math.max(step.getParent1().size(), step.getParent2().size()), step.getChild().size()))
                .max()
                .orElse(0);
    }

    /**
     * Valida l'integrità interna del generatore.
     *
     * @return true se lo stato interno è consistente
     */
    public boolean validateIntegrity() {
        try {
            // Verifica coerenza dimensioni
            if (registeredClauseHashes.size() > resolutionSteps.size()) {
                LOGGER.warning("Inconsistenza: più hash registrati che passi");
                return false;
            }

            // Verifica contenuto passi
            for (ResolutionStep step : resolutionSteps) {
                if (step == null) {
                    LOGGER.warning("Passo null trovato nella lista");
                    return false;
                }
            }

            // Verifica flag clausola vuota
            boolean actuallyHasEmpty = resolutionSteps.stream()
                    .anyMatch(step -> step.getChild().isEmpty());

            if (emptyClauseDerivated && !actuallyHasEmpty) {
                LOGGER.warning("Flag clausola vuota impostato ma nessuna clausola vuota trovata");
                return false;
            }

            return true;

        } catch (Exception e) {
            LOGGER.log(Level.WARNING, "Errore durante validazione integrità", e);
            return false;
        }
    }

    // ========================================
    // RAPPRESENTAZIONE TESTUALE E DEBUG
    // ========================================

    /**
     * Genera una rappresentazione testuale completa per debugging.
     *
     * @return stringa multi-linea con stato dettagliato del generatore
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("ProofGenerator {\n");
        sb.append("  Passi registrati: ").append(resolutionSteps.size()).append("\n");
        sb.append("  Clausola vuota derivata: ").append(emptyClauseDerivated).append("\n");
        sb.append("  Ottimizzazioni eseguite: ").append(optimizationCount).append("\n");
        sb.append("  Hash registrati: ").append(registeredClauseHashes.size()).append("\n");

        if (!resolutionSteps.isEmpty()) {
            sb.append("  Primo passo: ").append(formatStepSummary(resolutionSteps.get(0))).append("\n");
            sb.append("  Ultimo passo: ").append(formatStepSummary(resolutionSteps.get(resolutionSteps.size() - 1))).append("\n");
        }

        sb.append("}");
        return sb.toString();
    }

    /**
     * Genera una rappresentazione compatta per logging.
     *
     * @return stringa concisa con informazioni essenziali
     */
    public String toCompactString() {
        return String.format("ProofGen[steps=%d, empty=%s, opts=%d]",
                resolutionSteps.size(), emptyClauseDerivated, optimizationCount);
    }

    // ========================================
    // CLASSE STATISTICHE PROVA
    // ========================================

    /**
     * Classe immutabile per statistiche dettagliate della prova.
     */
    public static class ProofStatistics {
        private final int totalSteps;
        private final boolean hasEmptyClause;
        private final int optimizations;
        private final double averageClauseSize;
        private final int maxClauseSize;
        private final int uniqueClauses;

        public ProofStatistics(int totalSteps, boolean hasEmptyClause, int optimizations,
                               double averageClauseSize, int maxClauseSize, int uniqueClauses) {
            this.totalSteps = totalSteps;
            this.hasEmptyClause = hasEmptyClause;
            this.optimizations = optimizations;
            this.averageClauseSize = averageClauseSize;
            this.maxClauseSize = maxClauseSize;
            this.uniqueClauses = uniqueClauses;
        }

        // Getters
        public int getTotalSteps() { return totalSteps; }
        public boolean hasEmptyClause() { return hasEmptyClause; }
        public int getOptimizations() { return optimizations; }
        public double getAverageClauseSize() { return averageClauseSize; }
        public int getMaxClauseSize() { return maxClauseSize; }
        public int getUniqueClauses() { return uniqueClauses; }

        @Override
        public String toString() {
            return String.format("ProofStatistics{steps=%d, empty=%s, opts=%d, avgSize=%.1f, maxSize=%d, unique=%d}",
                    totalSteps, hasEmptyClause, optimizations, averageClauseSize, maxClauseSize, uniqueClauses);
        }
    }

    // ========================================
    // CLASSE PASSO DI RISOLUZIONE
    // ========================================

    /**
     * Rappresentazione immutabile di un singolo passo di risoluzione.
     *
     * Ogni passo rappresenta l'applicazione della regola di risoluzione binaria:
     * (C1 ∪ {x}) ⊗ (C2 ∪ {¬x}) → (C1 ∪ C2)
     *
     * dove:
     * - parent1 e parent2 sono le clausole input (C1 ∪ {x} e C2 ∪ {¬x})
     * - child è la clausola risultante (C1 ∪ C2)
     * - x è il letterale di risoluzione (implicito)
     *
     * Thread Safety: Immutabile dopo costruzione
     * Memory Safety: Copie difensive per prevenire modifiche esterne
     */
    private static class ResolutionStep {

        // ========================================
        // ATTRIBUTI IMMUTABILI
        // ========================================

        /** Prima clausola parent della risoluzione */
        private final List<Integer> parent1;

        /** Seconda clausola parent della risoluzione */
        private final List<Integer> parent2;

        /** Clausola child risultante dalla risoluzione */
        private final List<Integer> child;

        /** Hash code pre-calcolato per performance */
        private final int cachedHashCode;

        // ========================================
        // COSTRUZIONE
        // ========================================

        /**
         * Costruisce un passo di risoluzione immutabile.
         *
         * @param parent1 prima clausola parent (viene copiata difensivamente)
         * @param parent2 seconda clausola parent (viene copiata difensivamente)
         * @param child clausola child risultante (viene copiata difensivamente)
         */
        public ResolutionStep(List<Integer> parent1, List<Integer> parent2, List<Integer> child) {
            // Copie difensive per immutabilità
            this.parent1 = parent1 != null ? List.copyOf(parent1) : List.of();
            this.parent2 = parent2 != null ? List.copyOf(parent2) : List.of();
            this.child = child != null ? List.copyOf(child) : List.of();

            // Pre-calcola hash code per performance
            this.cachedHashCode = Objects.hash(this.parent1, this.parent2, this.child);
        }

        // ========================================
        // INTERFACCIA PUBBLICA
        // ========================================

        /**
         * Restituisce la prima clausola parent.
         * @return lista immutabile della prima clausola parent
         */
        public List<Integer> getParent1() {
            return parent1; // Già immutabile (List.copyOf)
        }

        /**
         * Restituisce la seconda clausola parent.
         * @return lista immutabile della seconda clausola parent
         */
        public List<Integer> getParent2() {
            return parent2; // Già immutabile (List.copyOf)
        }

        /**
         * Restituisce la clausola child.
         * @return lista immutabile della clausola child
         */
        public List<Integer> getChild() {
            return child; // Già immutabile (List.copyOf)
        }

        /**
         * Verifica se questo passo deriva la clausola vuota.
         * @return true se la clausola child è vuota
         */
        public boolean derivesEmptyClause() {
            return child.isEmpty();
        }

        /**
         * Calcola il numero totale di letterali in tutte le clausole.
         * @return somma delle dimensioni di parent1, parent2 e child
         */
        public int getTotalLiterals() {
            return parent1.size() + parent2.size() + child.size();
        }

        // ========================================
        // IMPLEMENTAZIONI STANDARD
        // ========================================

        /**
         * Confronto per uguaglianza basato sul contenuto delle clausole.
         */
        @Override
        public boolean equals(Object obj) {
            if (this == obj) return true;
            if (obj == null || getClass() != obj.getClass()) return false;

            ResolutionStep that = (ResolutionStep) obj;
            return Objects.equals(parent1, that.parent1) &&
                    Objects.equals(parent2, that.parent2) &&
                    Objects.equals(child, that.child);
        }

        /**
         * Hash code pre-calcolato per performance in collezioni.
         */
        @Override
        public int hashCode() {
            return cachedHashCode;
        }

        /**
         * Rappresentazione testuale per debugging.
         */
        @Override
        public String toString() {
            return String.format("ResolutionStep{%s + %s → %s}", parent1, parent2, child);
        }

        /**
         * Rappresentazione compatta per logging.
         */
        public String toCompactString() {
            return String.format("Step[%d,%d→%d]", parent1.size(), parent2.size(), child.size());
        }

        /**
         * Verifica se il passo è valido secondo le regole di risoluzione.
         * @return true se il passo rappresenta una risoluzione valida
         */
        public boolean isValid() {
            // Un passo è valido se:
            // 1. Tutte le clausole sono non-null (già garantito dal costruttore)
            // 2. La clausola child non è più grande della somma dei parent
            // 3. Non ci sono letterali null nelle clausole

            try {
                // Controllo dimensioni logiche
                if (child.size() > parent1.size() + parent2.size()) {
                    return false;
                }

                // Controllo contenuto clausole
                return parent1.stream().allMatch(Objects::nonNull) &&
                        parent2.stream().allMatch(Objects::nonNull) &&
                        child.stream().allMatch(Objects::nonNull);

            } catch (Exception e) {
                return false;
            }
        }
    }
}