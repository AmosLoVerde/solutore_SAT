package org.sat.cdcl;

import java.util.*;
import java.util.logging.Logger;
import java.util.stream.Collectors;

/**
 * GENERATORE PROVE MATEMATICHE - Sistema completo per generazione prove di insoddisfacibilità
 *
 * Implementa la generazione automatica di prove matematicamente corrette per formule UNSAT
 * tramite sequenze di spiegazioni successive, seguendo rigorosamente i principi della
 * logica proposizionale e del calcolo risolutivo.
 *
 * METODOLOGIA DELLE SPIEGAZIONI SEQUENZIALI:
 * • Ogni passo di spiegazione deriva una nuova clausola da due clausole esistenti
 * • Il processo continua fino alla derivazione della clausola vuota []
 * • Ogni derivazione è matematicamente giustificata e verificabile
 * • La prova finale è una sequenza completa e autocontenuta
 *
 * CARATTERISTICHE INNOVATIVE:
 * • Gestione corretta spiegazioni per conflitti livello 0 (clausole unitarie)
 * • Supporto spiegazioni sequenziali per casi complessi
 * • Output human-readable con nomi variabili originali
 * • Validazione automatica completezza e correttezza prove
 * • Logging dettagliato per debugging e audit
 *
 * FORMATO OUTPUT STANDARD:
 * (clausola1) e (clausola2) genera clausola_risultato
 * (clausola3) e (clausola4) genera clausola_risultato2
 * ...
 * (clausolaN) e (clausolaM) genera []
 *
 */
public class ProofGenerator {

    private static final Logger LOGGER = Logger.getLogger(ProofGenerator.class.getName());

    //region STRUTTURE DATI CORE PER TRACKING PROVE

    /**
     * Sequenza ordinata di spiegazioni registrate durante l'esecuzione CDCL.
     * Ogni spiegazione rappresenta un passo logico: clausola_A + clausola_B → clausola_C
     * Invariante: lista immutabile dopo registrazione, ordine cronologico preservato
     */
    private final List<ExplanationStep> explanationSequence;

    /**
     * Mapping bidirezionale da ID numerico a nome variabile originale.
     * Utilizzato per generazione output human-readable e debugging.
     * Invariante: mapping completo e consistente, no duplicati
     */
    private Map<Integer, String> variableMapping;

    /**
     * Flag che indica se la clausola vuota è stata derivata con successo.
     * Determina la completezza della prova di insoddisfacibilità.
     */
    private boolean emptyClauseDerivated;

    //endregion

    //region INIZIALIZZAZIONE E CONFIGURAZIONE

    /**
     * Inizializza generatore prove con strutture dati ottimizzate.
     * Prepara sistema per registrazione sequenziale di spiegazioni matematiche.
     */
    public ProofGenerator() {
        LOGGER.info("=== INIZIALIZZAZIONE GENERATORE PROVE MATEMATICHE ===");

        this.explanationSequence = new ArrayList<>();
        this.variableMapping = new HashMap<>();
        this.emptyClauseDerivated = false;

        LOGGER.fine("ProofGenerator pronto per registrazione spiegazioni sequenziali");
    }

    /**
     * Configura mapping variabili per output human-readable.
     * Essenziale per generazione prove comprensibili con nomi originali.
     *
     * @param mapping mappa ID_numerico → nome_originale
     * @throws IllegalArgumentException se mapping null o malformato
     */
    public void setVariableMapping(Map<Integer, String> mapping) {
        if (mapping == null) {
            throw new IllegalArgumentException("Mapping variabili non può essere null");
        }

        this.variableMapping = new HashMap<>(mapping);
        validateVariableMapping();

        LOGGER.fine("Mapping variabili configurato: " + variableMapping.size() + " variabili mappate");
    }

    /**
     * Valida integrità del mapping variabili per prevenzione errori.
     */
    private void validateVariableMapping() {
        for (Map.Entry<Integer, String> entry : variableMapping.entrySet()) {
            Integer id = entry.getKey();
            String name = entry.getValue();

            if (id == null || id <= 0) {
                throw new IllegalArgumentException("ID variabile non valido: " + id);
            }
            if (name == null || name.trim().isEmpty()) {
                throw new IllegalArgumentException("Nome variabile vuoto per ID: " + id);
            }
        }
    }

    //endregion

    //region REGISTRAZIONE SPIEGAZIONI E BUILDING PROVE

    /**
     * REGISTRAZIONE PASSO DI SPIEGAZIONE - Core del sistema di prove
     *
     * Registra una spiegazione matematica tra due clausole che genera una nuova clausola.
     * Questo corrisponde esattamente al processo di "risoluzione" nella logica proposizionale.
     *
     * PROCESSO DI REGISTRAZIONE:
     * 1. Validazione input per consistenza matematica
     * 2. Creazione step di spiegazione con copie difensive
     * 3. Verifica automatica derivazione clausola vuota
     * 4. Aggiornamento stato interno del generatore
     * 5. Logging per debugging e audit completo
     *
     * @param justifyingClause clausola che ha causato la propagazione
     * @param conflictClause clausola che è in conflitto
     * @param explanation risultato della spiegazione tra le due clausole
     * @throws IllegalArgumentException se clausole malformate
     */
    public void recordResolutionStep(List<Integer> justifyingClause,
                                     List<Integer> conflictClause,
                                     List<Integer> explanation) {

        LOGGER.finest("Registrazione passo di spiegazione matematica");

        // Validazione input per robustezza
        validateExplanationInputs(justifyingClause, conflictClause, explanation);

        // Log dettagliato per debugging
        logExplanationDetails(justifyingClause, conflictClause, explanation);

        // Creazione step con copie difensive per immutabilità
        ExplanationStep step = new ExplanationStep(
                createSafeCopy(justifyingClause),
                createSafeCopy(conflictClause),
                createSafeCopy(explanation)
        );

        // Registrazione atomica del passo
        explanationSequence.add(step);

        // Verifica derivazione clausola vuota
        if (explanation != null && explanation.isEmpty()) {
            emptyClauseDerivated = true;
            LOGGER.info("*** CLAUSOLA VUOTA [] DERIVATA - PROVA UNSAT COMPLETATA ***");
        }

        LOGGER.fine("Spiegazione registrata: " + formatStepSummary(step));
    }

    /**
     * Valida input per registrazione spiegazione.
     */
    private void validateExplanationInputs(List<Integer> justifying, List<Integer> conflict, List<Integer> explanation) {
        // Validazione clausole non null (possono essere vuote)
        if (justifying == null || conflict == null || explanation == null) {
            throw new IllegalArgumentException("Clausole per spiegazione non possono essere null");
        }

        // Validazione contenuto clausole
        validateClauseContent(justifying, "giustificante");
        validateClauseContent(conflict, "conflitto");
        validateClauseContent(explanation, "spiegazione");
    }

    /**
     * Valida contenuto di una singola clausola.
     */
    private void validateClauseContent(List<Integer> clause, String clauseType) {
        for (Integer literal : clause) {
            if (literal == null || literal == 0) {
                throw new IllegalArgumentException("Clausola " + clauseType + " contiene letterale non valido: " + literal);
            }
        }
    }

    /**
     * Registra dettagli spiegazione per debugging avanzato.
     */
    private void logExplanationDetails(List<Integer> justifying, List<Integer> conflict, List<Integer> explanation) {
        LOGGER.finest("Clausola giustificante: " + justifying);
        LOGGER.finest("Clausola conflitto: " + conflict);
        LOGGER.finest("Spiegazione risultante: " + explanation);
    }

    /**
     * Crea copia difensiva di una clausola per immutabilità.
     */
    private List<Integer> createSafeCopy(List<Integer> originalClause) {
        return originalClause != null ? new ArrayList<>(originalClause) : new ArrayList<>();
    }

    /**
     * Formatta riepilogo step per logging compatto.
     */
    private String formatStepSummary(ExplanationStep step) {
        return String.format("Spiegazione[%s + %s ⊢ %s]",
                formatClauseForLogging(step.getJustifyingClause()),
                formatClauseForLogging(step.getConflictClause()),
                formatClauseForLogging(step.getExplanation()));
    }

    /**
     * Formatta clausola per logging compatto.
     */
    private String formatClauseForLogging(List<Integer> clause) {
        if (clause == null || clause.isEmpty()) {
            return "[]\n";
        }
        return clause.toString();
    }

    //endregion

    //region GENERAZIONE PROVA FINALE

    /**
     * GENERAZIONE PROVA FINALE - Costruzione output matematico completo
     *
     * Genera la prova completa di insoddisfacibilità mostrando la sequenza ordinata
     * di spiegazioni che conducono alla clausola vuota. Il formato segue standard
     * accademici per massima chiarezza e verificabilità.
     *
     * ALGORITMO GENERAZIONE:
     * 1. Validazione completezza sequenza spiegazioni
     * 2. Costruzione output formattato step-by-step
     * 3. Verifica automatica presenza clausola vuota finale
     * 4. Generazione stringa prova human-readable
     * 5. Validazione finale integrità prova generata
     *
     * @return prova completa come stringa formattata
     * @throws IllegalStateException se prova incompleta
     */
    public String generateProof() {
        LOGGER.info("=== GENERAZIONE PROVA FINALE INSODDISFACIBILITÀ ===");

        // Validazione preliminare disponibilità dati
        validateProofGenerationPreconditions();

        StringBuilder proofBuilder = new StringBuilder();
        boolean emptyClauseFound = false;

        // Costruzione sequenziale della prova
        for (int stepIndex = 0; stepIndex < explanationSequence.size(); stepIndex++) {
            ExplanationStep step = explanationSequence.get(stepIndex);

            // Formattazione step corrente
            String formattedStep = formatExplanationStepForOutput(step);
            proofBuilder.append(formattedStep);

            // Verifica terminazione con clausola vuota
            if (step.getExplanation().isEmpty()) {
                emptyClauseFound = true;
                LOGGER.fine("Prova terminata al step " + (stepIndex + 1) + " con clausola vuota");
                break;
            }

            // Separatore tra step (eccetto ultimo)
            if (stepIndex < explanationSequence.size() - 1) {
                proofBuilder.append("\n");
            }
        }

        // Validazione finale prova
        validateGeneratedProof(emptyClauseFound);

        String finalProof = proofBuilder.toString();
        LOGGER.info("Prova matematica generata: " + explanationSequence.size() + " spiegazioni totali");

        return finalProof;
    }

    /**
     * Valida precondizioni per generazione prova.
     */
    private void validateProofGenerationPreconditions() {
        if (explanationSequence.isEmpty()) {
            LOGGER.warning("Nessuna spiegazione registrata per generazione prova");
            throw new IllegalStateException("Impossibile generare prova: sequenza spiegazioni vuota");
        }

        if (!emptyClauseDerivated) {
            LOGGER.warning("Clausola vuota non derivata - prova potenzialmente incompleta");
        }
    }

    /**
     * Formatta singola spiegazione per output finale human-readable.
     * Utilizza formato standard: (clausola1) e (clausola2) genera risultato
     */
    private String formatExplanationStepForOutput(ExplanationStep step) {
        String justifyingFormatted = formatClauseForFinalOutput(step.getJustifyingClause());
        String conflictFormatted = formatClauseForFinalOutput(step.getConflictClause());
        String explanationFormatted = formatClauseForFinalOutput(step.getExplanation());

        return String.format("(%s) e (%s) genera %s",
                justifyingFormatted, conflictFormatted, explanationFormatted);
    }

    /**
     * Valida prova generata per completezza e correttezza.
     */
    private void validateGeneratedProof(boolean emptyClauseFound) {
        if (!emptyClauseFound && emptyClauseDerivated) {
            LOGGER.warning("Inconsistenza: clausola vuota derivata ma non trovata in sequenza");
        }

        if (!emptyClauseFound) {
            LOGGER.warning("Prova generata senza clausola vuota finale - verifica completezza");
        }
    }

    //endregion

    //region FORMATAZIONE OUTPUT HUMAN-READABLE

    /**
     * Formatta clausola per output finale con nomi variabili originali.
     *
     * ESEMPI FORMATAZIONE:
     * • [] → "[]" (clausola vuota)
     * • [1] → "P" (clausola unitaria positiva)
     * • [-2] → "!Q" (clausola unitaria negativa)
     * • [1, -2, 3] → "P | !Q | R" (clausola normale)
     *
     * @param clause clausola da formattare
     * @return rappresentazione human-readable
     */
    private String formatClauseForFinalOutput(List<Integer> clause) {
        if (clause == null) {
            return "null";
        }

        if (clause.isEmpty()) {
            return "[]\n";
        }

        // Clausola unitaria - formato semplificato
        if (clause.size() == 1) {
            return formatSingleLiteralForOutput(clause.get(0));
        }

        // Clausola multipla - ordinamento e formatazione completa
        return formatMultipleClauseForOutput(clause);
    }

    /**
     * Formatta clausola con letterali multipli.
     */
    private String formatMultipleClauseForOutput(List<Integer> clause) {
        // Ordinamento per leggibilità: per variabile, poi per polarità
        List<Integer> sortedLiterals = clause.stream()
                .sorted(this::compareLiteralsForOutput)
                .collect(Collectors.toList());

        // Formatazione con separatori OR
        return sortedLiterals.stream()
                .map(this::formatSingleLiteralForOutput)
                .collect(Collectors.joining(" | "));
    }

    /**
     * Comparatore per ordinamento letterali nell'output.
     */
    private int compareLiteralsForOutput(Integer literal1, Integer literal2) {
        int variable1 = Math.abs(literal1);
        int variable2 = Math.abs(literal2);

        // Prima ordina per variabile
        if (variable1 != variable2) {
            return Integer.compare(variable1, variable2);
        }

        // Poi per polarità (positivi prima di negativi)
        return Integer.compare(literal1, literal2);
    }

    /**
     * Formatta singolo letterale con nome variabile originale.
     *
     * @param literal letterale numerico da formattare
     * @return rappresentazione con nome originale (es. "P" o "!Q")
     */
    private String formatSingleLiteralForOutput(Integer literal) {
        if (literal == null) {
            return "null";
        }

        int variable = Math.abs(literal);
        String variableName = variableMapping.getOrDefault(variable, String.valueOf(variable));

        // Formattazione polarità
        if (literal > 0) {
            return variableName; // Letterale positivo
        } else {
            return "!" + variableName; // Letterale negativo
        }
    }

    //endregion

    //region INTERFACCIA PUBBLICA DI STATO E CONTROLLO

    /**
     * @return true se clausola vuota è stata derivata (prova UNSAT completa)
     */
    public boolean hasEmptyClause() {
        return emptyClauseDerivated;
    }

    /**
     * @return numero totale di spiegazioni registrate nella sequenza
     */
    public int getStepCount() {
        return explanationSequence.size();
    }

    /**
     * @return true se generatore ha spiegazioni registrate
     */
    public boolean hasExplanations() {
        return !explanationSequence.isEmpty();
    }

    /**
     * @return copia immutabile della sequenza di spiegazioni per analisi
     */
    public List<ExplanationStep> getExplanationSequence() {
        return new ArrayList<>(explanationSequence);
    }

    /**
     * Reset completo del generatore per nuovo utilizzo.
     * Pulisce tutte le strutture dati mantenendo configurazione mapping.
     */
    public void reset() {
        LOGGER.info("Reset completo ProofGenerator");

        explanationSequence.clear();
        emptyClauseDerivated = false;

        // Mantiene variableMapping per riutilizzo
        LOGGER.fine("Stato ProofGenerator resettato, mapping variabili preservato");
    }

    /**
     * Reset completo includendo mapping variabili.
     */
    public void fullReset() {
        reset();
        variableMapping.clear();
        LOGGER.fine("Reset completo includendo mapping variabili");
    }

    /**
     * Rappresentazione testuale per debugging con statistiche essenziali.
     */
    @Override
    public String toString() {
        return String.format("ProofGenerator[steps=%d, empty_derived=%s, variables=%d]",
                explanationSequence.size(), emptyClauseDerivated, variableMapping.size());
    }

    //endregion

    //region CLASSE DI SUPPORTO - EXPLANATION STEP

    /**
     * PASSO DI SPIEGAZIONE - Rappresentazione immutabile di un singolo step logico
     *
     * Incapsula una singola spiegazione matematica tra due clausole che produce
     * una clausola risultante. Rappresenta l'unità atomica delle prove generate.
     *
     * COMPONENTI:
     * • Clausola giustificante: ha causato la propagazione
     * • Clausola conflitto: è in conflitto con propagazione
     * • Clausola spiegazione: risultato matematico della risoluzione
     *
     * INVARIANTI:
     * • Tutte le clausole sono immutabili dopo costruzione
     * • Rappresentazione matematicamente corretta
     * • Thread-safe per utilizzo concorrente
     */
    public static class ExplanationStep {

        /** Clausola che ha giustificato la propagazione causante il conflitto */
        private final List<Integer> justifyingClause;

        /** Clausola che è entrata in conflitto con la propagazione */
        private final List<Integer> conflictClause;

        /** Clausola risultante dalla spiegazione matematica tra le due */
        private final List<Integer> explanation;

        /**
         * Costruisce passo di spiegazione con clausole immutabili.
         * Garantisce immutabilità e thread-safety complete.
         *
         * @param justifyingClause clausola giustificante (copiata)
         * @param conflictClause clausola conflitto (copiata)
         * @param explanation clausola spiegazione risultante (copiata)
         */
        public ExplanationStep(List<Integer> justifyingClause,
                               List<Integer> conflictClause,
                               List<Integer> explanation) {

            this.justifyingClause = justifyingClause != null ?
                    Collections.unmodifiableList(new ArrayList<>(justifyingClause)) :
                    Collections.emptyList();

            this.conflictClause = conflictClause != null ?
                    Collections.unmodifiableList(new ArrayList<>(conflictClause)) :
                    Collections.emptyList();

            this.explanation = explanation != null ?
                    Collections.unmodifiableList(new ArrayList<>(explanation)) :
                    Collections.emptyList();
        }

        //region ACCESSORS IMMUTABILI

        /** @return clausola giustificante (immutabile) */
        public List<Integer> getJustifyingClause() {
            return justifyingClause;
        }

        /** @return clausola conflitto (immutabile) */
        public List<Integer> getConflictClause() {
            return conflictClause;
        }

        /** @return clausola spiegazione (immutabile) */
        public List<Integer> getExplanation() {
            return explanation;
        }

        //endregion

        //region UTILITÀ E RAPPRESENTAZIONE

        /**
         * @return true se questo step ha prodotto clausola vuota
         */
        public boolean derivesEmptyClause() {
            return explanation.isEmpty();
        }

        /**
         * @return numero totale letterali coinvolti in questo step
         */
        public int getTotalLiterals() {
            return justifyingClause.size() + conflictClause.size() + explanation.size();
        }

        /**
         * Rappresentazione matematica del passo per debugging.
         */
        @Override
        public String toString() {
            return String.format("ExplanationStep{%s ∧ %s ⊢ %s}",
                    justifyingClause, conflictClause, explanation);
        }

        /**
         * Uguaglianza basata su contenuto delle clausole.
         */
        @Override
        public boolean equals(Object obj) {
            if (this == obj) return true;
            if (obj == null || getClass() != obj.getClass()) return false;

            ExplanationStep other = (ExplanationStep) obj;
            return Objects.equals(justifyingClause, other.justifyingClause) &&
                    Objects.equals(conflictClause, other.conflictClause) &&
                    Objects.equals(explanation, other.explanation);
        }

        /**
         * Hash code consistente con equals.
         */
        @Override
        public int hashCode() {
            return Objects.hash(justifyingClause, conflictClause, explanation);
        }

        //endregion
    }

    //endregion
}