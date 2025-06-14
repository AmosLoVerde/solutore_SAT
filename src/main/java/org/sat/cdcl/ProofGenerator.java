package org.sat.cdcl;

import java.util.*;
import java.util.logging.Logger;
import java.util.stream.Collectors;

/**
 * GENERATORE PROVE MATEMATICHE - Sistema per costruzione prove di insoddisfacibilità
 *
 * Implementa la generazione automatica di prove matematiche per formule UNSAT seguendo
 * il metodo delle spiegazioni sequenziali. Ogni passo deriva una nuova clausola da due
 * clausole esistenti fino alla derivazione della clausola vuota [].
 *
 * METODOLOGIA:
 * - Ogni spiegazione: clausola_A + clausola_B -> clausola_spiegazione
 * - Sequenza ordinata di spiegazioni matematicamente giustificate
 * - Terminazione con clausola vuota [] per conferma UNSAT
 *
 * FORMATO OUTPUT:
 * (clausola1) e (clausola2) genera clausola_spiegazione1
 * (clausola3) e (clausola4) genera clausola_spiegazione2
 * ...
 * (clausolaN) e (clausolaM) genera []
 *
 */
public class ProofGenerator {

    private static final Logger LOGGER = Logger.getLogger(ProofGenerator.class.getName());

    //region STRUTTURE DATI CORE

    /**
     * Sequenza cronologica di spiegazioni matematiche registrate durante CDCL.
     * Ogni elemento rappresenta un passo: clausola_A + clausola_B → clausola_C
     */
    private final List<ExplanationStep> explanationSequence;

    /**
     * Mapping da ID numerico a nome variabile originale per output leggibile.
     * Essenziale per convertire prove numeriche in formato comprensibile.
     */
    private Map<Integer, String> variableMapping;

    /**
     * Indica se la clausola vuota [] è stata derivata con successo.
     * Determina la completezza della prova di insoddisfacibilità.
     */
    private boolean emptyClauseDerivated;

    //endregion

    //region INIZIALIZZAZIONE

    /**
     * Inizializza generatore prove con strutture dati pulite.
     * Prepara il sistema per registrazione sequenziale di spiegazioni.
     */
    public ProofGenerator() {
        LOGGER.info("Inizializzazione ProofGenerator per prove matematiche");

        this.explanationSequence = new ArrayList<>();
        this.variableMapping = new HashMap<>();
        this.emptyClauseDerivated = false;

        LOGGER.fine("ProofGenerator pronto per registrazione spiegazioni");
    }

    /**
     * Configura mapping variabili per output con nomi originali.
     * Necessario per generare prove comprensibili dall'utente.
     *
     * @param mapping mappa ID_numerico → nome_originale delle variabili
     * @throws IllegalArgumentException se mapping null o malformato
     */
    public void setVariableMapping(Map<Integer, String> mapping) {
        if (mapping == null) {
            throw new IllegalArgumentException("Mapping variabili non può essere null");
        }

        this.variableMapping = new HashMap<>(mapping);
        validateVariableMapping();

        LOGGER.fine("Mapping variabili configurato: " + variableMapping.size() + " variabili");
    }

    /**
     * Valida integrità del mapping variabili per prevenire errori di output.
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

    //region REGISTRAZIONE SPIEGAZIONI

    /**
     * CORE: Registra un passo di spiegazione matematica nella sequenza di prova.
     *
     * Questo è il cuore del sistema di prove. Ogni chiamata registra una derivazione
     * logica tra due clausole che produce una nuova clausola tramite risoluzione.
     *
     * PROCESSO:
     * 1. Valida input per consistenza matematica
     * 2. Crea step immutabile con copie difensive
     * 3. Verifica se è stata derivata la clausola vuota []
     * 4. Aggiorna stato interno del generatore
     *
     * @param justifyingClause clausola che ha causato la propagazione
     * @param conflictClause clausola che è entrata in conflitto
     * @param explanation risultato della risoluzione tra le due clausole
     * @throws IllegalArgumentException se clausole malformate
     */
    public void recordResolutionStep(List<Integer> justifyingClause,
                                     List<Integer> conflictClause,
                                     List<Integer> explanation) {

        LOGGER.finest("Registrazione passo di spiegazione matematica");

        // Validazione robusta dell'input
        validateExplanationInputs(justifyingClause, conflictClause, explanation);

        // Creazione step con copie difensive per immutabilità
        ExplanationStep step = new ExplanationStep(
                createSafeCopy(justifyingClause),
                createSafeCopy(conflictClause),
                createSafeCopy(explanation)
        );

        // Registrazione atomica del passo
        explanationSequence.add(step);

        // Verifica cruciale: clausola vuota derivata?
        if (explanation != null && explanation.isEmpty()) {
            emptyClauseDerivated = true;
            LOGGER.info("*** CLAUSOLA VUOTA [] DERIVATA - PROVA UNSAT COMPLETATA ***");
        }

        LOGGER.fine("Spiegazione registrata: " + formatStepSummary(step));
    }

    /**
     * Valida che tutti gli input per la registrazione siano corretti.
     * Verifica che le clausole non siano null e contengano letterali validi.
     */
    private void validateExplanationInputs(List<Integer> justifying, List<Integer> conflict, List<Integer> explanation) {
        if (justifying == null || conflict == null || explanation == null) {
            throw new IllegalArgumentException("Clausole per spiegazione non possono essere null");
        }

        validateClauseContent(justifying, "giustificante");
        validateClauseContent(conflict, "conflitto");
        validateClauseContent(explanation, "spiegazione");
    }

    /**
     * Valida che una clausola contenga solo letterali validi (non null, non zero).
     */
    private void validateClauseContent(List<Integer> clause, String clauseType) {
        for (Integer literal : clause) {
            if (literal == null || literal == 0) {
                throw new IllegalArgumentException("Clausola " + clauseType + " contiene letterale non valido: " + literal);
            }
        }
    }

    /**
     * Crea copia difensiva di una clausola per garantire immutabilità.
     */
    private List<Integer> createSafeCopy(List<Integer> originalClause) {
        return originalClause != null ? new ArrayList<>(originalClause) : new ArrayList<>();
    }

    /**
     * Formatta riepilogo compatto di uno step per logging.
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
        return (clause == null || clause.isEmpty()) ? "[]" : clause.toString();
    }

    //endregion

    //region GENERAZIONE PROVA FINALE

    /**
     * CORE: Genera la prova completa di insoddisfacibilità in formato human-readable.
     *
     * Costruisce la sequenza ordinata di spiegazioni che conducono alla clausola vuota.
     * Il formato segue standard accademici per massima chiarezza e verificabilità.
     *
     * ALGORITMO:
     * 1. Valida che esistano spiegazioni registrate
     * 2. Formatta ogni step nella sequenza
     * 3. Verifica che termini con clausola vuota []
     * 4. Restituisce prova completa come stringa
     *
     * @return prova matematica completa in formato standard
     * @throws IllegalStateException se prova incompleta o malformata
     */
    public String generateProof() {
        LOGGER.info("=== GENERAZIONE PROVA FINALE INSODDISFACIBILITÀ ===");

        validateProofPreconditions();

        StringBuilder proofBuilder = new StringBuilder();
        boolean emptyClauseFound = false;

        // Costruzione sequenziale della prova
        for (int stepIndex = 0; stepIndex < explanationSequence.size(); stepIndex++) {
            ExplanationStep step = explanationSequence.get(stepIndex);

            // Formatta step corrente in formato standard
            String formattedStep = formatExplanationStep(step);
            proofBuilder.append(formattedStep);

            // Verifica terminazione con clausola vuota
            if (step.getExplanation().isEmpty()) {
                emptyClauseFound = true;
                LOGGER.fine("Prova terminata al step " + (stepIndex + 1) + " con clausola vuota");
                break;
            }

            // Separatore tra step
            if (stepIndex < explanationSequence.size() - 1) {
                proofBuilder.append("\n");
            }
        }

        validateGeneratedProof(emptyClauseFound);

        String finalProof = proofBuilder.toString();
        LOGGER.info("Prova matematica generata: " + explanationSequence.size() + " spiegazioni totali");

        return finalProof;
    }

    /**
     * Verifica che ci siano le precondizioni per generare una prova valida.
     */
    private void validateProofPreconditions() {
        if (explanationSequence.isEmpty()) {
            LOGGER.warning("Nessuna spiegazione registrata per generazione prova");
            throw new IllegalStateException("Impossibile generare prova: sequenza spiegazioni vuota");
        }

        if (!emptyClauseDerivated) {
            LOGGER.warning("Clausola vuota non derivata - prova potenzialmente incompleta");
        }
    }

    /**
     * Formatta singola spiegazione nel formato standard di output.
     * Formato: (clausola1) e (clausola2) genera risultato
     */
    private String formatExplanationStep(ExplanationStep step) {
        String justifyingFormatted = formatClauseForOutput(step.getJustifyingClause());
        String conflictFormatted = formatClauseForOutput(step.getConflictClause());
        String explanationFormatted = formatClauseForOutput(step.getExplanation());

        return String.format("(%s) e (%s) genera (%s)\n",
                justifyingFormatted, conflictFormatted, explanationFormatted);
    }

    /**
     * Valida che la prova generata sia completa e corretta.
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
     * Formatta clausola per output finale usando nomi variabili originali.
     *
     * FORMATI:
     * • [] → "[]" (clausola vuota)
     * • [1] → "P" (clausola unitaria positiva)
     * • [-2] → "!Q" (clausola unitaria negativa)
     * • [1, -2, 3] → "P | !Q | R" (clausola normale)
     *
     * @param clause clausola da formattare
     * @return rappresentazione human-readable
     */
    private String formatClauseForOutput(List<Integer> clause) {
        if (clause == null) {
            return "null";
        }

        if (clause.isEmpty()) {
            return "[]";
        }

        if (clause.size() == 1) {
            return formatSingleLiteral(clause.get(0));
        }

        return formatMultipleClause(clause);
    }

    /**
     * Formatta clausola con letterali multipli ordinati per leggibilità.
     */
    private String formatMultipleClause(List<Integer> clause) {
        // Ordinamento per leggibilità: prima per variabile, poi per polarità
        List<Integer> sortedLiterals = clause.stream()
                .sorted(this::compareLiterals)
                .collect(Collectors.toList());

        // Unione con separatori OR
        return sortedLiterals.stream()
                .map(this::formatSingleLiteral)
                .collect(Collectors.joining(" | "));
    }

    /**
     * Comparatore per ordinamento letterali: prima variabile, poi polarità.
     */
    private int compareLiterals(Integer literal1, Integer literal2) {
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
    private String formatSingleLiteral(Integer literal) {
        if (literal == null) {
            return "null";
        }

        int variable = Math.abs(literal);
        String variableName = variableMapping.getOrDefault(variable, String.valueOf(variable));

        return literal > 0 ? variableName : "!" + variableName;
    }

    //endregion

    //region INTERFACCIA PUBBLICA E STATO

    /**
     * Verifica se la clausola vuota è stata derivata (prova UNSAT completa).
     */
    public boolean hasEmptyClause() {
        return emptyClauseDerivated;
    }

    /**
     * Restituisce numero totale di spiegazioni registrate.
     */
    public int getStepCount() {
        return explanationSequence.size();
    }

    /**
     * Verifica se il generatore ha spiegazioni registrate.
     */
    public boolean hasExplanations() {
        return !explanationSequence.isEmpty();
    }

    /**
     * Restituisce copia immutabile della sequenza di spiegazioni per analisi.
     */
    public List<ExplanationStep> getExplanationSequence() {
        return new ArrayList<>(explanationSequence);
    }

    /**
     * Reset completo del generatore mantenendo il mapping variabili.
     * Utile per riutilizzo su nuova formula con stesse variabili.
     */
    public void reset() {
        LOGGER.info("Reset ProofGenerator");

        explanationSequence.clear();
        emptyClauseDerivated = false;

        LOGGER.fine("Stato resettato, mapping variabili preservato");
    }

    /**
     * Reset completo includendo mapping variabili.
     * Usare per cambio completo di formula e variabili.
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

    //region CLASSE EXPLANATION STEP

    /**
     * PASSO DI SPIEGAZIONE - Rappresentazione immutabile di una derivazione logica
     *
     * Incapsula una singola spiegazione matematica tra due clausole che produce
     * una clausola risultante. Unità atomica delle prove generate.
     *
     * COMPONENTI:
     * • Clausola giustificante: ha causato la propagazione
     * • Clausola conflitto: è entrata in conflitto con propagazione
     * • Clausola spiegazione: risultato matematico della risoluzione
     */
    public static class ExplanationStep {

        private final List<Integer> justifyingClause;
        private final List<Integer> conflictClause;
        private final List<Integer> explanation;

        /**
         * Costruisce passo di spiegazione con clausole immutabili.
         * Garantisce thread-safety e immutabilità complete.
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

        /**
         * Restituisce clausola giustificante (immutabile).
         */
        public List<Integer> getJustifyingClause() {
            return justifyingClause;
        }

        /**
         * Restituisce clausola conflitto (immutabile).
         */
        public List<Integer> getConflictClause() {
            return conflictClause;
        }

        /**
         * Restituisce clausola spiegazione risultante (immutabile).
         */
        public List<Integer> getExplanation() {
            return explanation;
        }

        /**
         * Verifica se questo step ha prodotto la clausola vuota [].
         */
        public boolean derivesEmptyClause() {
            return explanation.isEmpty();
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
    }

    //endregion
}