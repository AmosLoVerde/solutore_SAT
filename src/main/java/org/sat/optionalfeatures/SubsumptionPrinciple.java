package org.sat.optionalfeatures;

import org.sat.cnf.CNFConverter;
import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;

/**
 * PRINCIPIO DI SUSSUNZIONE - Ottimizzazione avanzata per eliminazione clausole ridondanti
 *
 * Implementa il principio matematico di sussunzione per l'ottimizzazione di formule CNF,
 * eliminando clausole ridondanti che sono sovrainsieme di altre clausole più specifiche,
 * mantenendo perfetta equivalenza logica della formula.
 *
 * TEORIA MATEMATICA:
 * Una clausola C1 sussume una clausola C2 se e solo se:
 * • Tutti i letterali di C1 sono contenuti in C2 (C1 ⊆ C2)
 * • C2 può essere eliminata senza alterare la soddisfacibilità
 * • La formula risultante è logicamente equivalente all'originale
 *
 * ALGORITMO IMPLEMENTATO:
 * • Conversione clausole in rappresentazione Set per confronti O(1)
 * • Confronto sistematico a coppie tra tutte le clausole
 * • Identificazione relazioni di sussunzione bidirezionali
 * • Eliminazione clausole sussumete (più generali)
 * • Ricostruzione formula ottimizzata mantenendo struttura
 *
 * BENEFICI OTTIMIZZAZIONE:
 * • Riduzione spazio di ricerca per algoritmi SAT
 * • Miglioramento performance propagazione
 * • Semplificazione formula senza perdita informazioni
 * • Debugging facilitato con formule più compatte
 *
 * ESEMPI PRATICI:
 * Formula: (P) ∧ (!R ∨ !Q) ∧ (P ∨ Q ∨ !R) ∧ (A ∨ !R ∨ B ∨ !Q) ∧ (R ∨ !Q)
 * • (P) sussume (P ∨ Q ∨ !R) → elimina (P ∨ Q ∨ !R)
 * • (!R ∨ !Q) sussume (A ∨ !R ∨ B ∨ !Q) → elimina (A ∨ !R ∨ B ∨ !Q)
 * Risultato: (P) ∧ (!R ∨ !Q) ∧ (R ∨ !Q)
 *
 */
public class SubsumptionPrinciple {

    private static final Logger LOGGER = Logger.getLogger(SubsumptionPrinciple.class.getName());

    //region STATO OTTIMIZZAZIONE E TRACKING

    /**
     * Log dettagliato delle operazioni di ottimizzazione per reporting e debugging.
     * Contiene cronologia completa: formula originale, clausole eliminate, statistiche.
     */
    private StringBuilder optimizationLog;

    /**
     * Numero di clausole eliminate durante l'ottimizzazione.
     * Metrica chiave per valutare efficacia dell'ottimizzazione.
     */
    private int eliminatedClausesCount;

    /**
     * Numero di clausole presenti nella formula originale.
     * Utilizzato per calcolo percentuali di riduzione.
     */
    private int originalClausesCount;

    //endregion

    //region INIZIALIZZAZIONE E CONFIGURAZIONE

    /**
     * Inizializza ottimizzatore con stato pulito pronto per nuova elaborazione.
     * Prepara strutture dati per tracking completo del processo di ottimizzazione.
     */
    public SubsumptionPrinciple() {
        resetOptimizationState();
        LOGGER.fine("SubsumptionPrinciple inizializzato e pronto");
    }

    /**
     * Reset completo dello stato per riutilizzo dell'istanza.
     * Pulisce tutti i dati di precedenti ottimizzazioni mantenendo configurazione.
     */
    private void resetOptimizationState() {
        this.optimizationLog = new StringBuilder();
        this.eliminatedClausesCount = 0;
        this.originalClausesCount = 0;
    }

    //endregion

    //region INTERFACCIA PUBBLICA PRINCIPALE

    /**
     * METODO PRINCIPALE - Applica principio di sussunzione alla formula CNF
     *
     * Esegue ottimizzazione completa eliminando clausole ridondanti tramite sussunzione,
     * garantendo equivalenza logica e tracciabilità completa del processo.
     *
     * PIPELINE OTTIMIZZAZIONE:
     * 1. Validazione e inizializzazione con logging dettagliato
     * 2. Estrazione clausole dalla struttura CNFConverter
     * 3. Conversione in rappresentazione Set per confronti efficienti
     * 4. Identificazione sistematica relazioni di sussunzione
     * 5. Eliminazione clausole ridondanti con tracking
     * 6. Ricostruzione formula ottimizzata preservando struttura
     * 7. Generazione report dettagliato con statistiche
     *
     * @param cnfFormula formula CNF da ottimizzare (non null)
     * @return formula CNF ottimizzata con clausole ridondanti eliminate
     * @throws IllegalArgumentException se formula null o malformata
     */
    public CNFConverter applySubsumption(CNFConverter cnfFormula) {
        // Fase 1: Inizializzazione e validazione robusta
        if (!initializeOptimization(cnfFormula)) {
            return cnfFormula; // Ritorna originale se problemi rilevati
        }

        try {
            // Fase 2: Estrazione e conversione clausole
            List<Set<String>> clauseSetRepresentation = extractClausesAsSetRepresentation(cnfFormula);

            if (clauseSetRepresentation.isEmpty()) {
                logNoOptimizationCase("Formula vuota o senza clausole valide");
                return cnfFormula;
            }

            // Fase 3: Esecuzione ottimizzazione sussunzione
            List<Set<String>> optimizedClauseSets = executeSubsumptionOptimization(clauseSetRepresentation);

            // Fase 4: Ricostruzione formula dalla rappresentazione ottimizzata
            CNFConverter optimizedFormula = reconstructFormulaFromSets(optimizedClauseSets);

            // Fase 5: Finalizzazione con report completo
            finalizeOptimizationWithReport();

            return optimizedFormula;

        } catch (Exception e) {
            return handleOptimizationError(e, cnfFormula);
        }
    }

    //endregion

    //region INIZIALIZZAZIONE E VALIDAZIONE

    /**
     * Inizializza processo di ottimizzazione con validazione completa dell'input.
     *
     * @param cnfFormula formula da validare e preparare
     * @return true se inizializzazione successful, false altrimenti
     */
    private boolean initializeOptimization(CNFConverter cnfFormula) {
        resetOptimizationState();
        optimizationLog.append("=== INIZIO OTTIMIZZAZIONE SUSSUNZIONE ===\n");

        if (cnfFormula == null) {
            LOGGER.warning("Formula CNF null fornita all'ottimizzatore");
            optimizationLog.append("ERRORE: Formula null non processabile\n");
            return false;
        }

        String formulaRepresentation = getFormulaStringRepresentation(cnfFormula);
        optimizationLog.append("Formula originale: ").append(formulaRepresentation).append("\n");

        LOGGER.fine("Inizio ottimizzazione sussunzione per formula: " + formulaRepresentation);
        return true;
    }

    /**
     * Gestisce caso di nessuna ottimizzazione necessaria con logging appropriato.
     */
    private void logNoOptimizationCase(String reason) {
        optimizationLog.append("Nessuna ottimizzazione applicabile: ").append(reason).append("\n");
        LOGGER.fine("Ottimizzazione sussunzione non necessaria: " + reason);
    }

    /**
     * Gestisce errori durante ottimizzazione con fallback sicuro.
     */
    private CNFConverter handleOptimizationError(Exception e, CNFConverter originalFormula) {
        LOGGER.log(Level.WARNING, "Errore durante ottimizzazione sussunzione", e);
        optimizationLog.append("ERRORE: ").append(e.getMessage()).append("\n");
        optimizationLog.append("Fallback: ritornata formula originale\n");
        return originalFormula; // Fallback sicuro
    }

    //endregion

    //region ESTRAZIONE E CONVERSIONE CLAUSOLE

    /**
     * Estrae clausole dalla formula CNF e le converte in rappresentazione Set ottimizzata.
     * Ogni clausola diventa Set<String> per confronti di sussunzione O(1).
     *
     * @param cnfFormula formula CNF da processare
     * @return lista di Set rappresentanti le clausole
     */
    private List<Set<String>> extractClausesAsSetRepresentation(CNFConverter cnfFormula) {
        List<Set<String>> clauseSets = new ArrayList<>();

        switch (cnfFormula.type) {
            case AND -> {
                // Formula normale: congiunzione di clausole multiple
                if (cnfFormula.operands != null) {
                    for (CNFConverter clause : cnfFormula.operands) {
                        Set<String> clauseSet = convertSingleClauseToSet(clause);
                        if (!clauseSet.isEmpty()) {
                            clauseSets.add(clauseSet);
                        }
                    }
                }
            }
            case OR, ATOM, NOT -> {
                // Formula singola clausola
                Set<String> clauseSet = convertSingleClauseToSet(cnfFormula);
                if (!clauseSet.isEmpty()) {
                    clauseSets.add(clauseSet);
                }
            }
            default -> {
                LOGGER.warning("Tipo formula non supportato per sussunzione: " + cnfFormula.type);
                optimizationLog.append("ATTENZIONE: Tipo non supportato ").append(cnfFormula.type).append("\n");
            }
        }

        originalClausesCount = clauseSets.size();
        optimizationLog.append("Clausole estratte: ").append(originalClausesCount).append("\n");

        // Log dettagliato clausole per debugging
        logExtractedClauses(clauseSets);

        return clauseSets;
    }

    /**
     * Converte singola clausola CNF in Set di letterali string per confronti efficienti.
     */
    private Set<String> convertSingleClauseToSet(CNFConverter clause) {
        Set<String> literals = new HashSet<>();

        switch (clause.type) {
            case OR -> {
                // Disgiunzione: raccoglie tutti i letterali
                if (clause.operands != null) {
                    for (CNFConverter literal : clause.operands) {
                        String literalString = extractLiteralAsString(literal);
                        if (literalString != null) {
                            literals.add(literalString);
                        }
                    }
                }
            }
            case ATOM, NOT -> {
                // Letterale singolo
                String literalString = extractLiteralAsString(clause);
                if (literalString != null) {
                    literals.add(literalString);
                }
            }
            default -> {
                LOGGER.warning("Tipo clausola non supportato nella conversione: " + clause.type);
            }
        }

        return literals;
    }

    /**
     * Estrae letterale come stringa normalizzata per confronti.
     */
    private String extractLiteralAsString(CNFConverter literal) {
        switch (literal.type) {
            case ATOM -> {
                return literal.atom != null ? literal.atom.trim() : null;
            }
            case NOT -> {
                if (literal.operand != null && literal.operand.type == CNFConverter.Type.ATOM) {
                    String atom = literal.operand.atom;
                    return atom != null ? "!" + atom.trim() : null;
                }
            }
            default -> {
                LOGGER.warning("Tipo letterale non riconosciuto: " + literal.type);
            }
        }
        return null;
    }

    /**
     * Log dettagliato delle clausole estratte per debugging.
     */
    private void logExtractedClauses(List<Set<String>> clauseSets) {
        for (int i = 0; i < clauseSets.size(); i++) {
            optimizationLog.append("  ").append(i + 1).append(". ").append(clauseSets.get(i)).append("\n");
        }
    }

    //endregion

    //region ALGORITMO SUSSUNZIONE CORE

    /**
     * Esegue l'algoritmo di ottimizzazione sussunzione con analisi sistematica.
     *
     * ALGORITMO:
     * 1. Confronto a coppie di tutte le clausole
     * 2. Verifica sussunzione bidirezionale per ogni coppia
     * 3. Marking clausole da eliminare senza rimozione immediata
     * 4. Costruzione risultato con clausole sopravvissute
     * 5. Logging dettagliato di tutte le sussunzioni trovate
     *
     * @param clauseSets rappresentazione Set delle clausole
     * @return clausole ottimizzate dopo eliminazione ridondanze
     */
    private List<Set<String>> executeSubsumptionOptimization(List<Set<String>> clauseSets) {
        optimizationLog.append("\n=== ANALISI SUSSUNZIONE SISTEMATICA ===\n");

        // Set per tracking clausole da eliminare (evita rimozione durante iterazione)
        Set<Integer> clausesToEliminate = new HashSet<>();

        // Confronto sistematico a coppie
        for (int i = 0; i < clauseSets.size(); i++) {
            if (clausesToEliminate.contains(i)) continue;

            Set<String> clauseA = clauseSets.get(i);

            for (int j = i + 1; j < clauseSets.size(); j++) {
                if (clausesToEliminate.contains(j)) continue;

                Set<String> clauseB = clauseSets.get(j);

                // Verifica sussunzione bidirezionale
                if (checkSubsumption(clauseA, clauseB)) {
                    // clauseA sussume clauseB → elimina clauseB (più generale)
                    clausesToEliminate.add(j);
                    eliminatedClausesCount++;

                    logSubsumptionFound(clauseA, clauseB, "A sussume B");

                } else if (checkSubsumption(clauseB, clauseA)) {
                    // clauseB sussume clauseA → elimina clauseA (più generale)
                    clausesToEliminate.add(i);
                    eliminatedClausesCount++;

                    logSubsumptionFound(clauseB, clauseA, "B sussume A");
                    break; // clauseA eliminata, passa alla successiva
                }
            }
        }

        // Costruzione risultato con clausole sopravvissute
        List<Set<String>> optimizedClauses = buildOptimizedClauseList(clauseSets, clausesToEliminate);

        logOptimizationResults(optimizedClauses.size());
        return optimizedClauses;
    }

    /**
     * Verifica matematica se clauseA sussume clauseB.
     * Sussunzione: clauseA ⊆ clauseB (A è contenuto in B).
     *
     * @param clauseA clausola potenzialmente sussumente
     * @param clauseB clausola potenzialmente sussumeta
     * @return true se clauseA sussume clauseB
     */
    private boolean checkSubsumption(Set<String> clauseA, Set<String> clauseB) {
        // A sussume B se tutti i letterali di A sono contenuti in B
        return clauseB.containsAll(clauseA);
    }

    /**
     * Costruisce lista ottimizzata escludendo clausole eliminate.
     */
    private List<Set<String>> buildOptimizedClauseList(List<Set<String>> original, Set<Integer> toEliminate) {
        List<Set<String>> optimized = new ArrayList<>();

        for (int i = 0; i < original.size(); i++) {
            if (!toEliminate.contains(i)) {
                optimized.add(original.get(i));
            }
        }

        return optimized;
    }

    /**
     * Log dettagliato di sussunzione trovata per tracciabilità.
     */
    private void logSubsumptionFound(Set<String> sussumente, Set<String> sussumeta, String description) {
        optimizationLog.append("SUSSUNZIONE: ").append(sussumente)
                .append(" sussume ").append(sussumeta)
                .append(" (").append(description).append(")\n");

        LOGGER.fine("Sussunzione identificata: " + sussumente + " sussume " + sussumeta);
    }

    /**
     * Log risultati complessivi dell'ottimizzazione.
     */
    private void logOptimizationResults(int finalClausesCount) {
        optimizationLog.append("Clausole eliminate: ").append(eliminatedClausesCount).append("\n");
        optimizationLog.append("Clausole finali: ").append(finalClausesCount).append("\n");
    }

    //endregion

    //region RICOSTRUZIONE FORMULA

    /**
     * Ricostruisce formula CNF da rappresentazione Set ottimizzata.
     * Mantiene struttura originale compatibile con CNFConverter.
     *
     * @param optimizedClauseSets clausole in formato Set ottimizzato
     * @return formula CNF ricostruita
     */
    private CNFConverter reconstructFormulaFromSets(List<Set<String>> optimizedClauseSets) {
        optimizationLog.append("\n=== RICOSTRUZIONE FORMULA OTTIMIZZATA ===\n");

        if (optimizedClauseSets.isEmpty()) {
            optimizationLog.append("Nessuna clausola rimasta → formula TRUE\n");
            return new CNFConverter("TRUE");
        }

        List<CNFConverter> cnfClauses = new ArrayList<>();

        for (Set<String> clauseSet : optimizedClauseSets) {
            CNFConverter reconstructedClause = reconstructSingleClause(clauseSet);
            if (reconstructedClause != null) {
                cnfClauses.add(reconstructedClause);
            }
        }

        // Costruzione formula finale con struttura appropriata
        return buildFinalFormulaStructure(cnfClauses);
    }

    /**
     * Ricostruisce singola clausola da Set di letterali.
     */
    private CNFConverter reconstructSingleClause(Set<String> clauseSet) {
        if (clauseSet.isEmpty()) {
            return null;
        }

        List<CNFConverter> literals = new ArrayList<>();

        for (String literalString : clauseSet) {
            CNFConverter literal = reconstructSingleLiteral(literalString);
            if (literal != null) {
                literals.add(literal);
            }
        }

        return buildClauseStructure(literals);
    }

    /**
     * Ricostruisce singolo letterale da rappresentazione string.
     */
    private CNFConverter reconstructSingleLiteral(String literalString) {
        if (literalString == null || literalString.trim().isEmpty()) {
            return null;
        }

        String cleanLiteral = literalString.trim();

        if (cleanLiteral.startsWith("!")) {
            // Letterale negativo
            String atom = cleanLiteral.substring(1).trim();
            if (!atom.isEmpty()) {
                return new CNFConverter(new CNFConverter(atom));
            }
        } else {
            // Letterale positivo
            return new CNFConverter(cleanLiteral);
        }

        return null;
    }

    /**
     * Costruisce struttura clausola appropriata basata su numero letterali.
     */
    private CNFConverter buildClauseStructure(List<CNFConverter> literals) {
        if (literals.isEmpty()) {
            return null;
        } else if (literals.size() == 1) {
            return literals.get(0);
        } else {
            return new CNFConverter(CNFConverter.Type.OR, literals);
        }
    }

    /**
     * Costruisce struttura formula finale appropriata.
     */
    private CNFConverter buildFinalFormulaStructure(List<CNFConverter> cnfClauses) {
        if (cnfClauses.isEmpty()) {
            return new CNFConverter("TRUE");
        } else if (cnfClauses.size() == 1) {
            return cnfClauses.get(0);
        } else {
            return new CNFConverter(CNFConverter.Type.AND, cnfClauses);
        }
    }

    //endregion

    //region FINALIZZAZIONE E REPORTING

    /**
     * Finalizza ottimizzazione con generazione report completo.
     */
    private void finalizeOptimizationWithReport() {
        optimizationLog.append("\n=== RISULTATI FINALI OTTIMIZZAZIONE ===\n");
        optimizationLog.append("Clausole originali: ").append(originalClausesCount).append("\n");
        optimizationLog.append("Clausole eliminate: ").append(eliminatedClausesCount).append("\n");
        optimizationLog.append("Clausole finali: ").append(originalClausesCount - eliminatedClausesCount).append("\n");

        if (originalClausesCount > 0) {
            double reductionPercentage = (double) eliminatedClausesCount / originalClausesCount * 100;
            optimizationLog.append("Riduzione percentuale: ").append(String.format("%.1f%%", reductionPercentage)).append("\n");
        }

        optimizationLog.append("===============================\n");

        LOGGER.info("Ottimizzazione sussunzione completata: " + eliminatedClausesCount + " clausole eliminate su " + originalClausesCount);
    }

    //endregion

    //region INTERFACCIA PUBBLICA INFORMAZIONI

    /**
     * Restituisce report dettagliato dell'ottimizzazione per output utente.
     * Formato strutturato per presentazione e documentazione risultati.
     *
     * @return stringa formattata con statistiche e dettagli completi
     */
    public String getOptimizationInfo() {
        StringBuilder report = new StringBuilder();

        // Header standardizzato
        report.append("----------------------------\n");
        report.append("| PRINCIPIO DI SUSSUNZIONE |\n");
        report.append("----------------------------\n");

        // Statistiche principali
        appendMainStatistics(report);

        // Dettagli processo se disponibili
        appendProcessDetails(report);

        return report.toString();
    }

    /**
     * Aggiunge statistiche principali al report.
     */
    private void appendMainStatistics(StringBuilder report) {
        report.append("Clausole originali: ").append(originalClausesCount).append("\n");
        report.append("Clausole eliminate: ").append(eliminatedClausesCount).append("\n");
        report.append("Clausole finali: ").append(originalClausesCount - eliminatedClausesCount).append("\n");

        if (originalClausesCount > 0) {
            double reductionPercentage = (double) eliminatedClausesCount / originalClausesCount * 100;
            report.append("Riduzione percentuale: ").append(String.format("%.1f%%", reductionPercentage)).append("\n");
        } else {
            report.append("Riduzione percentuale: 0.0%\n");
        }

        report.append("\n");
    }

    /**
     * Aggiunge dettagli del processo al report se disponibili.
     */
    private void appendProcessDetails(StringBuilder report) {
        String logContent = optimizationLog.toString();

        if (logContent.contains("Formula originale:")) {
            report.append("=== DETTAGLI PROCESSO ===\n");
            extractAndAppendProcessInfo(report, logContent);
        }
    }

    /**
     * Estrae e formatta informazioni processo dal log interno.
     */
    private void extractAndAppendProcessInfo(StringBuilder report, String logContent) {
        String[] logLines = logContent.split("\n");

        // Estrai informazioni chiave
        for (String line : logLines) {
            if (line.contains("Formula originale:")) {
                String formula = line.substring(line.indexOf(":") + 1).trim();
                report.append("Formula originale: ").append(formula).append("\n");
            } else if (line.contains("Clausole estratte:")) {
                report.append("Clausole estratte: ").append(line.substring(line.indexOf(":") + 1).trim()).append("\n");
            }
        }

        // Aggiungi sussunzioni trovate
        appendSubsumptionsFound(report, logLines);
    }

    /**
     * Aggiunge sussunzioni trovate al report.
     */
    private void appendSubsumptionsFound(StringBuilder report, String[] logLines) {
        boolean hasSubsumptions = false;

        for (String line : logLines) {
            if (line.contains("SUSSUNZIONE:")) {
                if (!hasSubsumptions) {
                    report.append("\n=== SUSSUNZIONI IDENTIFICATE ===\n");
                    hasSubsumptions = true;
                }

                String subsumption = line.substring(line.indexOf("SUSSUNZIONE:") + 12).trim();
                report.append(subsumption).append("\n");
            }
        }
    }

    /**
     * @return numero clausole eliminate durante ottimizzazione
     */
    public int getEliminatedClausesCount() {
        return eliminatedClausesCount;
    }

    /**
     * @return numero clausole originali prima dell'ottimizzazione
     */
    public int getOriginalClausesCount() {
        return originalClausesCount;
    }

    /**
     * @return percentuale di riduzione ottenuta (0.0-100.0)
     */
    public double getReductionPercentage() {
        return originalClausesCount > 0 ?
                (double) eliminatedClausesCount / originalClausesCount * 100 : 0.0;
    }

    /**
     * Reset completo per riutilizzo dell'istanza su nuova formula.
     */
    public void reset() {
        resetOptimizationState();
        LOGGER.fine("SubsumptionPrinciple resettato per nuovo utilizzo");
    }

    //endregion

    //region UTILITÀ E HELPER METHODS

    /**
     * Ottiene rappresentazione string sicura della formula per logging.
     */
    private String getFormulaStringRepresentation(CNFConverter formula) {
        try {
            return formula != null ? formula.toString() : "null";
        } catch (Exception e) {
            LOGGER.log(Level.WARNING, "Errore toString() su formula durante logging", e);
            return "ERROR_IN_FORMULA_REPRESENTATION";
        }
    }

    /**
     * Rappresentazione testuale dell'ottimizzatore per debugging.
     */
    @Override
    public String toString() {
        return String.format("SubsumptionPrinciple[original=%d, eliminated=%d, final=%d, reduction=%.1f%%]",
                originalClausesCount, eliminatedClausesCount,
                originalClausesCount - eliminatedClausesCount, getReductionPercentage());
    }

    //endregion
}