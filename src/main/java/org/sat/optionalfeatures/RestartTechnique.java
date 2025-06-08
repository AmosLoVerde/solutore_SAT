package org.sat.optionalfeatures;

import org.sat.cnf.CNFConverter;
import org.sat.support.DecisionStack;
import org.sat.support.AssignedLiteral;
import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;

/**
 * TECNICA DEL RESTART - Implementazione completa per prevenzione stalli in ricerca SAT
 *
 * Implementa la strategia di restart periodico per evitare stalli durante la ricerca SAT,
 * applicando reinizio ogni N conflitti con preservazione dell'apprendimento e applicazione
 * automatica della sussunzione per ottimizzazione post-restart.
 *
 * TEORIA E MOTIVAZIONI:
 * • Previene stalli in aree non promettenti dello spazio di ricerca
 * • Mantiene knowledge acquisition tramite clausole apprese
 * • Combina restart con sussunzione per duplice ottimizzazione
 * • Bilancia exploration vs exploitation nella ricerca
 *
 * ALGORITMO RESTART IMPLEMENTATO:
 * • Contatore conflitti con soglia configurabile (default: 5)
 * • Trigger automatico ogni N conflitti durante conflict analysis
 * • Preservazione completa: clausole apprese + assegnamenti livello 0
 * • Eliminazione decisionale: tutte le decisioni e propagazioni livelli > 0
 * • Sussunzione post-restart per rimozione clausole ridondanti
 * • Ripresa algoritmo normale da stato pulito livello 0
 *
 * BENEFICI PERFORMANCE:
 * • Riduzione probability di rimanere bloccati in subtree infruttuosi
 * • Migliore diversificazione della ricerca
 * • Sinergia restart + sussunzione per formula più compatta
 * • Mantenimento progressive learning tramite clausole
 *
 * INTEGRAZIONE CDCL:
 * • Trigger nel conflict analysis prima del backtracking
 * • Coordinamento con decision stack per gestione livelli
 * • Interfaccia pulita per disaccoppiamento da core solver
 * • Statistiche dettagliate per monitoraggio efficacia
 *
 */
public class RestartTechnique {

    private static final Logger LOGGER = Logger.getLogger(RestartTechnique.class.getName());

    //region CONFIGURAZIONE E SOGLIE

    /** Soglia conflitti per trigger restart (modificabile per tuning) */
    private static final int DEFAULT_CONFLICT_THRESHOLD = 5;

    /** Soglia conflitti corrente (può essere modificata dinamicamente) */
    private int conflictThreshold;

    //endregion

    //region STATO E TRACKING

    /**
     * Contatore conflitti corrente per trigger restart.
     * Reset dopo ogni restart per ciclo continuo.
     */
    private int currentConflictCount;

    /**
     * Numero totale restart eseguiti durante sessione.
     * Utilizzato per statistiche e tuning adattivo.
     */
    private int totalRestarts;

    /**
     * Ottimizzatore sussunzione per applicazione post-restart.
     * Condiviso per efficienza e stato persistente.
     */
    private final SubsumptionPrinciple subsumptionOptimizer;

    /**
     * Log dettagliato operazioni restart per debugging e reporting.
     * Contiene cronologia completa trigger, preservazioni, eliminazioni.
     */
    private final StringBuilder restartLog;

    /**
     * Clausole totali rimosse tramite sussunzione durante tutti i restart.
     * Metrica aggregata per valutazione efficacia combinata restart+sussunzione.
     */
    private int totalSubsumptionRemovals;

    //endregion

    //region INIZIALIZZAZIONE E CONFIGURAZIONE

    /**
     * Inizializza tecnica restart con configurazione default e stato pulito.
     * Prepara ottimizzatore sussunzione e strutture tracking integrate.
     */
    public RestartTechnique() {
        this(DEFAULT_CONFLICT_THRESHOLD);
    }

    /**
     * Inizializza tecnica restart con soglia personalizzata.
     *
     * @param conflictThreshold numero conflitti per trigger restart
     * @throws IllegalArgumentException se soglia < 1
     */
    public RestartTechnique(int conflictThreshold) {
        if (conflictThreshold < 1) {
            throw new IllegalArgumentException("Soglia conflitti deve essere >= 1, ricevuto: " + conflictThreshold);
        }

        this.conflictThreshold = conflictThreshold;
        this.currentConflictCount = 0;
        this.totalRestarts = 0;
        this.totalSubsumptionRemovals = 0;
        this.subsumptionOptimizer = new SubsumptionPrinciple();
        this.restartLog = new StringBuilder();

        logInitialization();
        LOGGER.fine("RestartTechnique inizializzata con soglia " + conflictThreshold + " conflitti");
    }

    /**
     * Log inizializzazione per tracking configurazione.
     */
    private void logInitialization() {
        restartLog.append("=== INIZIALIZZAZIONE RESTART TECHNIQUE ===\n");
        restartLog.append("Soglia conflitti: ").append(conflictThreshold).append("\n");
        restartLog.append("Sussunzione integrata: ATTIVA\n");
        restartLog.append("==========================================\n\n");
    }

    //endregion

    //region INTERFACCIA PUBBLICA PRINCIPALE

    /**
     * Registra nuovo conflitto e verifica se trigger restart.
     * Chiamato dal CDCLSolver ad ogni conflitto rilevato.
     *
     * @return true se restart deve essere attivato, false altrimenti
     */
    public boolean registerConflictAndCheckRestart() {
        currentConflictCount++;

        LOGGER.finest("Conflitto registrato: " + currentConflictCount + "/" + conflictThreshold);

        boolean shouldRestart = (currentConflictCount >= conflictThreshold);

        if (shouldRestart) {
            LOGGER.info("*** RESTART TRIGGER - Conflitto #" + currentConflictCount +
                    " ha raggiunto soglia " + conflictThreshold + " ***");

            restartLog.append("RESTART #").append(totalRestarts + 1)
                    .append(" - Trigger al conflitto ").append(currentConflictCount).append("\n");
        }

        return shouldRestart;
    }

    /**
     * METODO PRINCIPALE - Esegue restart completo con preservazione e ottimizzazione
     *
     * Coordina l'intera procedura restart mantenendo separazione delle responsabilità
     * tra gestione stato solver e ottimizzazioni interne restart.
     *
     * PROCESSO RESTART COMPLETO:
     * 1. Preservazione stato critico (livello 0, clausole apprese)
     * 2. Reset contatori e preparazione restart
     * 3. Applicazione sussunzione per ottimizzazione formula
     * 4. Logging dettagliato per monitoring e debugging
     * 5. Aggiornamento statistiche aggregate
     *
     * @param level0Assignments assegnamenti livello 0 da preservare
     * @param learnedClauses clausole apprese da mantenere e ottimizzare
     * @return informazioni dettagliate restart per feedback solver
     */
    public RestartResult executeRestart(List<AssignedLiteral> level0Assignments,
                                        List<List<Integer>> learnedClauses) {
        LOGGER.info("=== ESECUZIONE RESTART #" + (totalRestarts + 1) + " ===");

        try {
            // Step 1: Preservazione stato critico
            RestartPreservationData preservationData = preserveCriticalState(level0Assignments, learnedClauses);

            // Step 2: Reset contatori e preparazione
            prepareRestartExecution();

            // Step 3: Applicazione sussunzione ottimizzante
            SubsumptionResult subsumptionResult = applyPostRestartSubsumption(preservationData.learnedClauses);

            // Step 4: Costruzione risultato completo
            RestartResult result = buildRestartResult(preservationData, subsumptionResult);

            // Step 5: Finalizzazione con logging
            finalizeRestartWithLogging(result);

            return result;

        } catch (Exception e) {
            return handleRestartError(e, level0Assignments, learnedClauses);
        }
    }

    //endregion

    //region PRESERVAZIONE STATO CRITICO

    /**
     * Preserva stato critico che deve sopravvivere al restart.
     * Garantisce che informazioni essenziali non vadano perse.
     */
    private RestartPreservationData preserveCriticalState(List<AssignedLiteral> level0Assignments,
                                                          List<List<Integer>> learnedClauses) {
        LOGGER.fine("Preservazione stato critico per restart");

        // Copia difensiva assegnamenti livello 0
        List<AssignedLiteral> preservedLevel0 = level0Assignments != null ?
                new ArrayList<>(level0Assignments) : new ArrayList<>();

        // Copia difensiva clausole apprese
        List<List<Integer>> preservedClauses = new ArrayList<>();
        if (learnedClauses != null) {
            for (List<Integer> clause : learnedClauses) {
                preservedClauses.add(new ArrayList<>(clause));
            }
        }

        restartLog.append("Stato preservato: ")
                .append(preservedLevel0.size()).append(" assegnamenti livello 0, ")
                .append(preservedClauses.size()).append(" clausole apprese\n");

        LOGGER.fine("Stato critico preservato: " + preservedLevel0.size() + " assegnamenti, " +
                preservedClauses.size() + " clausole");

        return new RestartPreservationData(preservedLevel0, preservedClauses);
    }

    //endregion

    //region PREPARAZIONE E RESET

    /**
     * Prepara esecuzione restart con reset contatori e aggiornamento stato.
     */
    private void prepareRestartExecution() {
        totalRestarts++;
        currentConflictCount = 0; // Reset per prossimo ciclo

        restartLog.append("Reset contatore conflitti per nuovo ciclo\n");
        restartLog.append("Restart totali: ").append(totalRestarts).append("\n");

        LOGGER.fine("Preparazione restart completata - Restart #" + totalRestarts);
    }

    //endregion

    //region SUSSUNZIONE POST-RESTART

    /**
     * Applica sussunzione alle clausole apprese per ottimizzazione post-restart.
     * Sfrutta restart come opportunità per compattazione formula.
     */
    private SubsumptionResult applyPostRestartSubsumption(List<List<Integer>> learnedClauses) {
        LOGGER.info("Applicazione sussunzione post-restart...");

        if (learnedClauses == null || learnedClauses.isEmpty()) {
            restartLog.append("Nessuna clausola per sussunzione\n");
            return new SubsumptionResult(new ArrayList<>(), 0, "Nessuna clausola disponibile");
        }

        try {
            // Converte clausole numeriche in CNFConverter per sussunzione
            CNFConverter formulaForSubsumption = buildFormulaForSubsumption(learnedClauses);

            // Applica sussunzione
            CNFConverter optimizedFormula = subsumptionOptimizer.applySubsumption(formulaForSubsumption);

            // Estrae risultati ottimizzazione
            int removedClauses = subsumptionOptimizer.getEliminatedClausesCount();
            String subsumptionInfo = subsumptionOptimizer.getOptimizationInfo();

            // Riconverte in formato numerico
            List<List<Integer>> optimizedClauses = extractOptimizedClauses(optimizedFormula);

            // Aggiorna statistiche aggregate
            totalSubsumptionRemovals += removedClauses;

            restartLog.append("Sussunzione completata: ")
                    .append(removedClauses).append(" clausole rimosse\n");

            LOGGER.info("Sussunzione post-restart: " + removedClauses + " clausole eliminate, " +
                    optimizedClauses.size() + " clausole finali");

            return new SubsumptionResult(optimizedClauses, removedClauses, subsumptionInfo);

        } catch (Exception e) {
            LOGGER.log(Level.WARNING, "Errore durante sussunzione post-restart", e);
            restartLog.append("Errore sussunzione: ").append(e.getMessage()).append("\n");

            // Fallback: ritorna clausole originali
            return new SubsumptionResult(learnedClauses, 0, "Errore sussunzione - clausole non modificate");
        }
    }

    /**
     * Costruisce formula CNF da clausole numeriche per sussunzione.
     */
    private CNFConverter buildFormulaForSubsumption(List<List<Integer>> numericalClauses) {
        List<CNFConverter> cnfClauses = new ArrayList<>();

        for (List<Integer> numericalClause : numericalClauses) {
            CNFConverter cnfClause = convertNumericalClauseToCNF(numericalClause);
            if (cnfClause != null) {
                cnfClauses.add(cnfClause);
            }
        }

        if (cnfClauses.isEmpty()) {
            return new CNFConverter("TRUE");
        } else if (cnfClauses.size() == 1) {
            return cnfClauses.get(0);
        } else {
            return new CNFConverter(CNFConverter.Type.AND, cnfClauses);
        }
    }

    /**
     * Converte clausola numerica in CNFConverter.
     */
    private CNFConverter convertNumericalClauseToCNF(List<Integer> numericalClause) {
        if (numericalClause == null || numericalClause.isEmpty()) {
            return null;
        }

        List<CNFConverter> literals = new ArrayList<>();

        for (Integer literal : numericalClause) {
            Integer variable = Math.abs(literal);
            String variableName = "var" + variable; // Nome generico per sussunzione

            if (literal > 0) {
                literals.add(new CNFConverter(variableName));
            } else {
                literals.add(new CNFConverter(new CNFConverter(variableName)));
            }
        }

        if (literals.size() == 1) {
            return literals.get(0);
        } else {
            return new CNFConverter(CNFConverter.Type.OR, literals);
        }
    }

    /**
     * Estrae clausole ottimizzate dalla formula post-sussunzione.
     */
    private List<List<Integer>> extractOptimizedClauses(CNFConverter optimizedFormula) {
        List<List<Integer>> extractedClauses = new ArrayList<>();

        if (optimizedFormula == null) {
            return extractedClauses;
        }

        switch (optimizedFormula.type) {
            case AND -> {
                if (optimizedFormula.operands != null) {
                    for (CNFConverter clause : optimizedFormula.operands) {
                        List<Integer> numericalClause = convertCNFToNumericalClause(clause);
                        if (!numericalClause.isEmpty()) {
                            extractedClauses.add(numericalClause);
                        }
                    }
                }
            }
            case OR, ATOM, NOT -> {
                List<Integer> numericalClause = convertCNFToNumericalClause(optimizedFormula);
                if (!numericalClause.isEmpty()) {
                    extractedClauses.add(numericalClause);
                }
            }
        }

        return extractedClauses;
    }

    /**
     * Converte CNFConverter in clausola numerica.
     */
    private List<Integer> convertCNFToNumericalClause(CNFConverter cnfClause) {
        List<Integer> numericalClause = new ArrayList<>();

        if (cnfClause == null) {
            return numericalClause;
        }

        switch (cnfClause.type) {
            case OR -> {
                if (cnfClause.operands != null) {
                    for (CNFConverter literal : cnfClause.operands) {
                        Integer numericalLiteral = convertCNFToNumericalLiteral(literal);
                        if (numericalLiteral != null) {
                            numericalClause.add(numericalLiteral);
                        }
                    }
                }
            }
            case ATOM, NOT -> {
                Integer numericalLiteral = convertCNFToNumericalLiteral(cnfClause);
                if (numericalLiteral != null) {
                    numericalClause.add(numericalLiteral);
                }
            }
        }

        return numericalClause;
    }

    /**
     * Converte singolo letterale CNF in rappresentazione numerica.
     */
    private Integer convertCNFToNumericalLiteral(CNFConverter literal) {
        if (literal == null) {
            return null;
        }

        switch (literal.type) {
            case ATOM -> {
                if (literal.atom != null && literal.atom.startsWith("var")) {
                    try {
                        return Integer.parseInt(literal.atom.substring(3));
                    } catch (NumberFormatException e) {
                        LOGGER.warning("Formato variabile non riconosciuto: " + literal.atom);
                    }
                }
            }
            case NOT -> {
                if (literal.operand != null && literal.operand.type == CNFConverter.Type.ATOM) {
                    String atom = literal.operand.atom;
                    if (atom != null && atom.startsWith("var")) {
                        try {
                            return -Integer.parseInt(atom.substring(3));
                        } catch (NumberFormatException e) {
                            LOGGER.warning("Formato variabile negata non riconosciuto: " + atom);
                        }
                    }
                }
            }
        }

        return null;
    }

    //endregion

    //region COSTRUZIONE RISULTATO

    /**
     * Costruisce risultato completo restart con tutte le informazioni necessarie.
     */
    private RestartResult buildRestartResult(RestartPreservationData preservationData,
                                             SubsumptionResult subsumptionResult) {
        return new RestartResult(
                totalRestarts,
                preservationData.level0Assignments,
                subsumptionResult.optimizedClauses,
                subsumptionResult.removedClausesCount,
                totalSubsumptionRemovals,
                generateRestartSummary(preservationData, subsumptionResult)
        );
    }

    /**
     * Genera riepilogo testuale restart per logging e reporting.
     */
    private String generateRestartSummary(RestartPreservationData preservationData,
                                          SubsumptionResult subsumptionResult) {
        StringBuilder summary = new StringBuilder();
        summary.append("RESTART #").append(totalRestarts).append(" SUMMARY:\n");
        summary.append("- Assegnamenti livello 0 preservati: ").append(preservationData.level0Assignments.size()).append("\n");
        summary.append("- Clausole pre-sussunzione: ").append(preservationData.learnedClauses.size()).append("\n");
        summary.append("- Clausole post-sussunzione: ").append(subsumptionResult.optimizedClauses.size()).append("\n");
        summary.append("- Clausole rimosse: ").append(subsumptionResult.removedClausesCount).append("\n");
        summary.append("- Rimozioni totali: ").append(totalSubsumptionRemovals).append("\n");
        return summary.toString();
    }

    //endregion

    //region FINALIZZAZIONE E LOGGING

    /**
     * Finalizza restart con logging completo per monitoring.
     */
    private void finalizeRestartWithLogging(RestartResult result) {
        restartLog.append(result.summary).append("\n");

        LOGGER.info("=== RESTART #" + totalRestarts + " COMPLETATO ===");
        LOGGER.info("Preservati: " + result.preservedLevel0Assignments.size() + " assegnamenti livello 0");
        LOGGER.info("Ottimizzate: " + result.optimizedLearnedClauses.size() + " clausole finali");
        LOGGER.info("Rimosse: " + result.subsumptionRemovals + " clausole in questo restart");
        LOGGER.info("Rimozioni cumulative: " + result.totalSubsumptionRemovals + " clausole totali");
    }

    /**
     * Gestisce errori durante restart con fallback sicuro.
     */
    private RestartResult handleRestartError(Exception e, List<AssignedLiteral> level0Assignments,
                                             List<List<Integer>> learnedClauses) {
        LOGGER.log(Level.SEVERE, "Errore durante esecuzione restart", e);
        restartLog.append("ERRORE RESTART: ").append(e.getMessage()).append("\n");

        // Fallback: preserva stato senza modifiche
        List<AssignedLiteral> preservedLevel0 = level0Assignments != null ?
                new ArrayList<>(level0Assignments) : new ArrayList<>();
        List<List<Integer>> preservedClauses = learnedClauses != null ?
                new ArrayList<>(learnedClauses) : new ArrayList<>();

        totalRestarts++; // Conta anche restart falliti
        currentConflictCount = 0;

        return new RestartResult(
                totalRestarts,
                preservedLevel0,
                preservedClauses,
                0, // Nessuna rimozione per errore
                totalSubsumptionRemovals,
                "Restart #" + totalRestarts + " fallito: " + e.getMessage()
        );
    }

    //endregion

    //region INTERFACCIA PUBBLICA INFORMAZIONI

    /**
     * Verifica se restart è attualmente richiesto.
     * Metodo di convenienza per controlli esterni.
     */
    public boolean isRestartRequired() {
        return currentConflictCount >= conflictThreshold;
    }

    /**
     * @return numero totale restart eseguiti
     */
    public int getTotalRestarts() {
        return totalRestarts;
    }

    /**
     * @return numero conflitti corrente verso prossimo restart
     */
    public int getCurrentConflictCount() {
        return currentConflictCount;
    }

    /**
     * @return soglia conflitti per trigger restart
     */
    public int getConflictThreshold() {
        return conflictThreshold;
    }

    /**
     * @return clausole totali rimosse tramite sussunzione
     */
    public int getTotalSubsumptionRemovals() {
        return totalSubsumptionRemovals;
    }

    /**
     * Restituisce statistiche dettagliate per reporting.
     */
    public String getRestartStatistics() {
        StringBuilder stats = new StringBuilder();
        stats.append("=== STATISTICHE RESTART ===\n");
        stats.append("Restart totali: ").append(totalRestarts).append("\n");
        stats.append("Soglia conflitti: ").append(conflictThreshold).append("\n");
        stats.append("Conflitti correnti: ").append(currentConflictCount).append("/").append(conflictThreshold).append("\n");
        stats.append("Rimozioni sussunzione: ").append(totalSubsumptionRemovals).append("\n");

        if (totalRestarts > 0) {
            double avgRemovals = (double) totalSubsumptionRemovals / totalRestarts;
            stats.append("Media rimozioni/restart: ").append(String.format("%.1f", avgRemovals)).append("\n");
        }

        stats.append("===========================\n");
        return stats.toString();
    }

    /**
     * Restituisce log completo restart per debugging dettagliato.
     */
    public String getDetailedRestartLog() {
        return restartLog.toString();
    }

    /**
     * Reset completo per nuovo utilizzo.
     */
    public void reset() {
        currentConflictCount = 0;
        totalRestarts = 0;
        totalSubsumptionRemovals = 0;
        restartLog.setLength(0);
        subsumptionOptimizer.reset();

        logInitialization();
        LOGGER.fine("RestartTechnique resettata completamente");
    }

    /**
     * Modifica soglia conflitti dinamicamente.
     */
    public void setConflictThreshold(int newThreshold) {
        if (newThreshold < 1) {
            throw new IllegalArgumentException("Soglia deve essere >= 1");
        }

        int oldThreshold = this.conflictThreshold;
        this.conflictThreshold = newThreshold;

        restartLog.append("Soglia modificata: ").append(oldThreshold).append(" → ").append(newThreshold).append("\n");
        LOGGER.info("Soglia restart cambiata: " + oldThreshold + " → " + newThreshold);
    }

    //endregion

    //region CLASSI DI SUPPORTO

    /**
     * Dati preservati durante restart per garantire continuità.
     */
    private static class RestartPreservationData {
        final List<AssignedLiteral> level0Assignments;
        final List<List<Integer>> learnedClauses;

        RestartPreservationData(List<AssignedLiteral> level0Assignments, List<List<Integer>> learnedClauses) {
            this.level0Assignments = level0Assignments;
            this.learnedClauses = learnedClauses;
        }
    }

    /**
     * Risultato sussunzione post-restart.
     */
    private static class SubsumptionResult {
        final List<List<Integer>> optimizedClauses;
        final int removedClausesCount;
        final String subsumptionInfo;

        SubsumptionResult(List<List<Integer>> optimizedClauses, int removedClausesCount, String subsumptionInfo) {
            this.optimizedClauses = optimizedClauses;
            this.removedClausesCount = removedClausesCount;
            this.subsumptionInfo = subsumptionInfo;
        }
    }

    /**
     * Risultato completo restart per comunicazione con solver.
     */
    public static class RestartResult {
        public final int restartNumber;
        public final List<AssignedLiteral> preservedLevel0Assignments;
        public final List<List<Integer>> optimizedLearnedClauses;
        public final int subsumptionRemovals;
        public final int totalSubsumptionRemovals;
        public final String summary;

        public RestartResult(int restartNumber, List<AssignedLiteral> preservedLevel0Assignments,
                             List<List<Integer>> optimizedLearnedClauses, int subsumptionRemovals,
                             int totalSubsumptionRemovals, String summary) {
            this.restartNumber = restartNumber;
            this.preservedLevel0Assignments = preservedLevel0Assignments;
            this.optimizedLearnedClauses = optimizedLearnedClauses;
            this.subsumptionRemovals = subsumptionRemovals;
            this.totalSubsumptionRemovals = totalSubsumptionRemovals;
            this.summary = summary;
        }
    }

    //endregion

    //region RAPPRESENTAZIONE TESTUALE

    /**
     * Rappresentazione testuale per debugging.
     */
    @Override
    public String toString() {
        return String.format("RestartTechnique[restarts=%d, threshold=%d, current=%d/%d, removals=%d]",
                totalRestarts, conflictThreshold, currentConflictCount, conflictThreshold, totalSubsumptionRemovals);
    }

    //endregion
}