package org.sat.cdcl;

import java.util.*;
import java.util.logging.Logger;
import java.util.stream.Collectors;

/**
 * GENERATORE PROVE CORRETTO per formule UNSAT tramite sequenza di spiegazioni
 *
 * Implementa la generazione di prove basata su spiegazioni successive come
 * descritto nella specifica corretta del CDCL. Ogni passo di spiegazione
 * viene registrato e la prova finale mostra la derivazione sequenziale
 * che porta alla clausola vuota [].
 */
public class ProofGenerator {

    private static final Logger LOGGER = Logger.getLogger(ProofGenerator.class.getName());

    //region STRUTTURE DATI PER TRACCIAMENTO PROVE

    /**
     * Sequenza di spiegazioni registrate durante il CDCL
     * Ogni spiegazione è: clausola_giustificante + clausola_conflitto → clausola_spiegazione
     */
    private final List<ExplanationStep> explanationSteps;

    /**
     * Mapping da ID numerico a nome variabile originale per output leggibile
     */
    private Map<Integer, String> variableMapping;

    /**
     * Flag che indica se la clausola vuota è stata derivata
     */
    private boolean emptyClauseDerivated;

    //endregion

    //region INIZIALIZZAZIONE

    /**
     * Inizializza generatore prove per sequenza di spiegazioni
     */
    public ProofGenerator() {
        LOGGER.info("=== INIZIALIZZAZIONE PROOF GENERATOR CORRETTO ===");

        this.explanationSteps = new ArrayList<>();
        this.variableMapping = new HashMap<>();
        this.emptyClauseDerivated = false;

        LOGGER.fine("ProofGenerator inizializzato per spiegazioni sequenziali");
    }

    /**
     * Configura mapping variabili per output leggibile
     */
    public void setVariableMapping(Map<Integer, String> mapping) {
        this.variableMapping = new HashMap<>(mapping);
        LOGGER.fine("Mapping variabili configurato: " + variableMapping.size() + " variabili");
    }

    //endregion

    //region REGISTRAZIONE SPIEGAZIONI

    /**
     * REGISTRAZIONE PASSO DI SPIEGAZIONE
     *
     * Registra una spiegazione tra clausola giustificante e clausola di conflitto.
     * Questo corrisponde esattamente al processo di "spiegazione" descritto nella specifica.
     *
     * @param justifyingClause clausola che ha causato la propagazione
     * @param conflictClause clausola che è in conflitto
     * @param explanation risultato della spiegazione tra le due clausole
     */
    public void recordResolutionStep(List<Integer> justifyingClause,
                                     List<Integer> conflictClause,
                                     List<Integer> explanation) {

        LOGGER.finest("Registrazione spiegazione");
        LOGGER.finest("Clausola giustificante: " + justifyingClause);
        LOGGER.finest("Clausola conflitto: " + conflictClause);
        LOGGER.finest("Spiegazione risultante: " + explanation);

        // Crea passo di spiegazione con defensive copying
        ExplanationStep step = new ExplanationStep(
                copyClauseDefensively(justifyingClause),
                copyClauseDefensively(conflictClause),
                copyClauseDefensively(explanation)
        );

        // Registra il passo
        explanationSteps.add(step);

        // Verifica se abbiamo derivato clausola vuota
        if (explanation != null && explanation.isEmpty()) {
            emptyClauseDerivated = true;
            LOGGER.info("*** CLAUSOLA VUOTA [] DERIVATA TRAMITE SPIEGAZIONE ***");
        }

        LOGGER.fine("Spiegazione registrata: " + formatStepSummary(step));
    }

    /**
     * Crea copia difensiva di una clausola
     */
    private List<Integer> copyClauseDefensively(List<Integer> originalClause) {
        return originalClause != null ? new ArrayList<>(originalClause) : new ArrayList<>();
    }

    /**
     * Formatta riepilogo di un passo per logging
     */
    private String formatStepSummary(ExplanationStep step) {
        return String.format("Spiegazione[%s + %s => %s]",
                formatClauseForDisplay(step.getJustifyingClause()),
                formatClauseForDisplay(step.getConflictClause()),
                formatClauseForDisplay(step.getExplanation()));
    }

    //endregion

    //region GENERAZIONE PROVA FINALE

    /**
     * GENERAZIONE PROVA FINALE
     *
     * Genera la prova completa mostrando la sequenza di spiegazioni che
     * portano alla clausola vuota. Il formato è quello descritto nella specifica:
     *
     * (clausola1) e (clausola2) genera clausola_risultato
     * (clausola3) e (clausola4) genera clausola_risultato2
     * ...
     * (clausolaN) e (clausolaM) genera []
     */
    public String generateProof() {
        LOGGER.info("=== GENERAZIONE PROVA FINALE DA SPIEGAZIONI ===");

        if (explanationSteps.isEmpty()) {
            LOGGER.warning("Nessuna spiegazione registrata per generazione prova");
            return "Errore: nessuna spiegazione disponibile per formula UNSAT";
        }

        StringBuilder proofBuilder = new StringBuilder();

        for (int i = 0; i < explanationSteps.size(); i++) {
            ExplanationStep step = explanationSteps.get(i);
            String formattedStep = formatExplanationStep(step);
            proofBuilder.append(formattedStep);

            // Verifica se questo è l'ultimo passo (clausola vuota)
            if (step.getExplanation().isEmpty()) {
                LOGGER.fine("Prova terminata al passo " + (i + 1) + " con clausola vuota");
                break;
            }

            if (i < explanationSteps.size() - 1) {
                proofBuilder.append("\n");
            }
        }

        String finalProof = proofBuilder.toString();
        LOGGER.info("Prova finale generata: " + explanationSteps.size() + " spiegazioni totali");

        return finalProof;
    }

    /**
     * Formatta singola spiegazione nel formato richiesto:
     * (clausola1) e (clausola2) genera clausola_risultato
     */
    private String formatExplanationStep(ExplanationStep step) {
        String justifying = formatClauseForDisplay(step.getJustifyingClause());
        String conflict = formatClauseForDisplay(step.getConflictClause());
        String explanation = formatClauseForDisplay(step.getExplanation());

        return String.format("(%s) e (%s) genera %s", justifying, conflict, explanation);
    }

    //endregion

    //region FORMATAZIONE OUTPUT

    /**
     * Formatta clausola per visualizzazione human-readable
     *
     * Esempi:
     * [] → []
     * [1] → P
     * [-2] → !Q
     * [1, -2] → P | !Q
     */
    private String formatClauseForDisplay(List<Integer> clause) {
        if (clause == null) {
            return "null";
        }

        if (clause.isEmpty()) {
            return "[]";
        }

        if (clause.size() == 1) {
            return formatSingleLiteralForDisplay(clause.get(0));
        }

        // Clausola multipla: ordinamento e formatazione
        List<Integer> sortedLiterals = clause.stream()
                .sorted((a, b) -> {
                    int variableA = Math.abs(a);
                    int variableB = Math.abs(b);
                    if (variableA != variableB) {
                        return Integer.compare(variableA, variableB);
                    }
                    return Integer.compare(a, b);
                })
                .collect(Collectors.toList());

        return sortedLiterals.stream()
                .map(this::formatSingleLiteralForDisplay)
                .collect(Collectors.joining(" | "));
    }

    /**
     * Formatta singolo letterale con nomi simbolici
     */
    private String formatSingleLiteralForDisplay(Integer literal) {
        if (literal == null) return "null";

        int variable = Math.abs(literal);
        String variableName = variableMapping.getOrDefault(variable, String.valueOf(variable));

        if (literal > 0) {
            return variableName;
        } else {
            return "!" + variableName;
        }
    }

    //endregion

    //region INTERFACCIA PUBBLICA DI STATO

    /**
     * @return true se clausola vuota è stata derivata
     */
    public boolean hasEmptyClause() {
        return emptyClauseDerivated;
    }

    /**
     * @return numero totale di spiegazioni registrate
     */
    public int getStepCount() {
        return explanationSteps.size();
    }

    /**
     * Reset completo del generatore
     */
    public void reset() {
        LOGGER.info("Reset completo ProofGenerator");
        explanationSteps.clear();
        variableMapping.clear();
        emptyClauseDerivated = false;
    }

    /**
     * Rappresentazione testuale per debugging
     */
    @Override
    public String toString() {
        return String.format("ProofGenerator[steps=%d, empty_derived=%s]",
                explanationSteps.size(), emptyClauseDerivated);
    }

    //endregion

    //region CLASSE DI SUPPORTO

    /**
     * PASSO DI SPIEGAZIONE
     *
     * Rappresenta una singola spiegazione tra clausola giustificante e
     * clausola di conflitto che produce una clausola risultante.
     */
    private static class ExplanationStep {

        /** Clausola che ha giustificato la propagazione */
        private final List<Integer> justifyingClause;

        /** Clausola che è in conflitto */
        private final List<Integer> conflictClause;

        /** Risultato della spiegazione */
        private final List<Integer> explanation;

        /**
         * Costruisce passo di spiegazione con clausole immutabili
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

        public List<Integer> getJustifyingClause() { return justifyingClause; }
        public List<Integer> getConflictClause() { return conflictClause; }
        public List<Integer> getExplanation() { return explanation; }

        @Override
        public String toString() {
            return String.format("ExplanationStep{%s + %s => %s}",
                    justifyingClause, conflictClause, explanation);
        }
    }

    //endregion
}