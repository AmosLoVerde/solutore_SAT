package org.sat.optionalfeatures;

import org.sat.cnf.CNFConverter;
import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;

/**
 * IMPLEMENTAZIONE DEL PRINCIPIO DI SUSSUNZIONE per ottimizzazione formule CNF
 *
 * Il principio di sussunzione elimina clausole ridondanti che sono sovrainsieme
 * di altre clausole più piccole, mantenendo l'equivalenza logica della formula.
 *
 * DEFINIZIONE:
 * Una clausola C1 sussume una clausola C2 se tutti i letterali di C1 sono
 * contenuti in C2. In questo caso C2 può essere eliminata senza alterare
 * la soddisfacibilità della formula.
 *
 * ESEMPIO:
 * Formula: (P) & (!R | !Q) & (P | Q | !R) & (A | !R | B | !Q) & (R | !Q)
 * - (P) sussume (P | Q | !R) → elimina (P | Q | !R)
 * - (!R | !Q) sussume (A | !R | B | !Q) → elimina (A | !R | B | !Q)
 * Risultato: (P) & (!R | !Q) & (R | !Q)
 *
 */
public class SubsumptionPrinciple {

    private static final Logger LOGGER = Logger.getLogger(SubsumptionPrinciple.class.getName());

    //region STATO OTTIMIZZAZIONE

    /** Statistiche di ottimizzazione */
    private StringBuilder optimizationLog;

    /** Contatore clausole eliminate */
    private int eliminatedClauses;

    /** Clausole originali prima dell'ottimizzazione */
    private int originalClauseCount;

    //endregion

    //region INIZIALIZZAZIONE

    /**
     * Costruttore che inizializza stato per nuova ottimizzazione
     */
    public SubsumptionPrinciple() {
        resetState();
        LOGGER.fine("SubsumptionPrinciple inizializzato");
    }

    /**
     * Reset stato per nuova ottimizzazione
     */
    private void resetState() {
        this.optimizationLog = new StringBuilder();
        this.eliminatedClauses = 0;
        this.originalClauseCount = 0;
    }

    //endregion

    //region INTERFACCIA PUBBLICA PRINCIPALE

    /**
     * METODO PRINCIPALE: Applica principio di sussunzione alla formula CNF
     *
     * ALGORITMO:
     * 1. Estrazione clausole dalla struttura CNFConverter
     * 2. Conversione in rappresentazione set per confronti efficienti
     * 3. Identificazione coppie sussunzione tra tutte le clausole
     * 4. Eliminazione clausole sussumete (sovrainsieme)
     * 5. Ricostruzione formula ottimizzata
     *
     * @param cnfFormula formula CNF da ottimizzare
     * @return formula CNF ottimizzata con clausole ridondanti eliminate
     */
    public CNFConverter applySubsumption(CNFConverter cnfFormula) {
        // Fase 1: Inizializzazione e validazione
        if (!initializeOptimization(cnfFormula)) {
            return cnfFormula; // Ritorna originale se problemi
        }

        try {
            // Fase 2: Estrazione clausole
            List<Set<String>> clauseSets = extractClausesAsSets(cnfFormula);

            if (clauseSets.isEmpty()) {
                logNoOptimizationNeeded("Formula vuota o senza clausole");
                return cnfFormula;
            }

            // Fase 3: Applicazione sussunzione
            List<Set<String>> optimizedClauseSets = performSubsumptionOptimization(clauseSets);

            // Fase 4: Ricostruzione formula
            CNFConverter optimizedFormula = reconstructFormula(optimizedClauseSets);

            // Fase 5: Logging finale
            logOptimizationResults();

            return optimizedFormula;

        } catch (Exception e) {
            LOGGER.log(Level.WARNING, "Errore durante ottimizzazione sussunzione", e);
            optimizationLog.append("ERRORE: ").append(e.getMessage()).append("\n");
            return cnfFormula; // Fallback sicuro
        }
    }

    //endregion

    //region INIZIALIZZAZIONE E VALIDAZIONE

    /**
     * Inizializza ottimizzazione con validazione input
     */
    private boolean initializeOptimization(CNFConverter cnfFormula) {
        resetState();
        optimizationLog.append("=== INIZIO OTTIMIZZAZIONE SUSSUNZIONE ===\n");

        if (cnfFormula == null) {
            LOGGER.warning("Formula CNF null fornita");
            optimizationLog.append("ERRORE: Formula null\n");
            return false;
        }

        String formulaStr = safeToString(cnfFormula);
        optimizationLog.append("Formula originale: ").append(formulaStr).append("\n");

        LOGGER.fine("Inizio ottimizzazione sussunzione");
        return true;
    }

    /**
     * Log quando ottimizzazione non necessaria
     */
    private void logNoOptimizationNeeded(String reason) {
        optimizationLog.append("Nessuna ottimizzazione necessaria: ").append(reason).append("\n");
        LOGGER.fine("Ottimizzazione sussunzione non necessaria: " + reason);
    }

    //endregion

    //region ESTRAZIONE CLAUSOLE

    /**
     * Estrae clausole dalla formula CNF e le converte in Set di stringhe
     * per confronti efficienti di sussunzione
     */
    private List<Set<String>> extractClausesAsSets(CNFConverter cnfFormula) {
        List<Set<String>> clauseSets = new ArrayList<>();

        switch (cnfFormula.type) {
            case AND -> {
                // Formula normale: congiunzione di clausole
                if (cnfFormula.operands != null) {
                    for (CNFConverter clause : cnfFormula.operands) {
                        Set<String> clauseSet = extractSingleClauseAsSet(clause);
                        if (!clauseSet.isEmpty()) {
                            clauseSets.add(clauseSet);
                        }
                    }
                }
            }
            case OR, ATOM, NOT -> {
                // Formula singola clausola
                Set<String> clauseSet = extractSingleClauseAsSet(cnfFormula);
                if (!clauseSet.isEmpty()) {
                    clauseSets.add(clauseSet);
                }
            }
            default -> {
                LOGGER.warning("Tipo formula non supportato per sussunzione: " + cnfFormula.type);
                optimizationLog.append("ATTENZIONE: Tipo non supportato ").append(cnfFormula.type).append("\n");
            }
        }

        originalClauseCount = clauseSets.size();
        optimizationLog.append("Clausole estratte: ").append(originalClauseCount).append("\n");

        // Log clausole per debugging
        for (int i = 0; i < clauseSets.size(); i++) {
            optimizationLog.append("  ").append(i + 1).append(". ").append(clauseSets.get(i)).append("\n");
        }

        return clauseSets;
    }

    /**
     * Estrae singola clausola come Set di letterali stringa
     */
    private Set<String> extractSingleClauseAsSet(CNFConverter clause) {
        Set<String> literals = new HashSet<>();

        switch (clause.type) {
            case OR -> {
                // Disgiunzione: raccoglie tutti i letterali
                if (clause.operands != null) {
                    for (CNFConverter literal : clause.operands) {
                        String literalStr = extractLiteralAsString(literal);
                        if (literalStr != null) {
                            literals.add(literalStr);
                        }
                    }
                }
            }
            case ATOM, NOT -> {
                // Letterale singolo
                String literalStr = extractLiteralAsString(clause);
                if (literalStr != null) {
                    literals.add(literalStr);
                }
            }
            default -> {
                LOGGER.warning("Tipo clausola non supportato: " + clause.type);
            }
        }

        return literals;
    }

    /**
     * Estrae letterale come stringa normalizzata
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

    //endregion

    //region ALGORITMO SUSSUNZIONE

    /**
     * Esegue l'ottimizzazione di sussunzione principale
     */
    private List<Set<String>> performSubsumptionOptimization(List<Set<String>> clauseSets) {
        optimizationLog.append("\n=== ANALISI SUSSUNZIONE ===\n");

        // Set per tracking clausole da eliminare
        Set<Integer> clausesToEliminate = new HashSet<>();

        // Confronto ogni coppia di clausole
        for (int i = 0; i < clauseSets.size(); i++) {
            if (clausesToEliminate.contains(i)) continue;

            Set<String> clause1 = clauseSets.get(i);

            for (int j = i + 1; j < clauseSets.size(); j++) {
                if (clausesToEliminate.contains(j)) continue;

                Set<String> clause2 = clauseSets.get(j);

                // Verifica sussunzione in entrambe le direzioni
                if (subsumes(clause1, clause2)) {
                    // clause1 sussume clause2 → elimina clause2
                    clausesToEliminate.add(j);
                    eliminatedClauses++;

                    optimizationLog.append("SUSSUNZIONE: ").append(clause1)
                            .append(" sussume ").append(clause2)
                            .append(" → elimina ").append(clause2).append("\n");

                    LOGGER.fine("Clausola " + clause1 + " sussume " + clause2);

                } else if (subsumes(clause2, clause1)) {
                    // clause2 sussume clause1 → elimina clause1
                    clausesToEliminate.add(i);
                    eliminatedClauses++;

                    optimizationLog.append("SUSSUNZIONE: ").append(clause2)
                            .append(" sussume ").append(clause1)
                            .append(" → elimina ").append(clause1).append("\n");

                    LOGGER.fine("Clausola " + clause2 + " sussume " + clause1);
                    break; // clause1 eliminata, passa alla prossima
                }
            }
        }

        // Costruisci lista clausole ottimizzate
        List<Set<String>> optimizedClauses = new ArrayList<>();
        for (int i = 0; i < clauseSets.size(); i++) {
            if (!clausesToEliminate.contains(i)) {
                optimizedClauses.add(clauseSets.get(i));
            }
        }

        optimizationLog.append("Clausole eliminate: ").append(eliminatedClauses).append("\n");
        optimizationLog.append("Clausole rimanenti: ").append(optimizedClauses.size()).append("\n");

        return optimizedClauses;
    }

    /**
     * Verifica se clausola1 sussume clausola2
     *
     * Una clausola C1 sussume C2 se tutti i letterali di C1 sono contenuti in C2
     */
    private boolean subsumes(Set<String> clause1, Set<String> clause2) {
        // C1 sussume C2 se C1 ⊆ C2
        return clause2.containsAll(clause1);
    }

    //endregion

    //region RICOSTRUZIONE FORMULA

    /**
     * Ricostruisce formula CNF da clausole ottimizzate
     */
    private CNFConverter reconstructFormula(List<Set<String>> optimizedClauseSets) {
        optimizationLog.append("\n=== RICOSTRUZIONE FORMULA ===\n");

        if (optimizedClauseSets.isEmpty()) {
            optimizationLog.append("Nessuna clausola rimanente → formula TRUE\n");
            return new CNFConverter("TRUE");
        }

        List<CNFConverter> cnfClauses = new ArrayList<>();

        for (Set<String> clauseSet : optimizedClauseSets) {
            CNFConverter clause = reconstructSingleClause(clauseSet);
            if (clause != null) {
                cnfClauses.add(clause);
            }
        }

        // Costruzione formula finale
        if (cnfClauses.isEmpty()) {
            return new CNFConverter("TRUE");
        } else if (cnfClauses.size() == 1) {
            return cnfClauses.get(0);
        } else {
            return new CNFConverter(CNFConverter.Type.AND, cnfClauses);
        }
    }

    /**
     * Ricostruisce singola clausola da Set di letterali
     */
    private CNFConverter reconstructSingleClause(Set<String> clauseSet) {
        if (clauseSet.isEmpty()) {
            return null;
        }

        List<CNFConverter> literals = new ArrayList<>();

        for (String literalStr : clauseSet) {
            CNFConverter literal = reconstructSingleLiteral(literalStr);
            if (literal != null) {
                literals.add(literal);
            }
        }

        if (literals.isEmpty()) {
            return null;
        } else if (literals.size() == 1) {
            return literals.get(0);
        } else {
            return new CNFConverter(CNFConverter.Type.OR, literals);
        }
    }

    /**
     * Ricostruisce singolo letterale da stringa
     */
    private CNFConverter reconstructSingleLiteral(String literalStr) {
        if (literalStr == null || literalStr.trim().isEmpty()) {
            return null;
        }

        literalStr = literalStr.trim();

        if (literalStr.startsWith("!")) {
            String atom = literalStr.substring(1).trim();
            if (!atom.isEmpty()) {
                return new CNFConverter(new CNFConverter(atom));
            }
        } else {
            return new CNFConverter(literalStr);
        }

        return null;
    }

    //endregion

    //region LOGGING E STATISTICHE

    /**
     * Log risultati finali ottimizzazione
     */
    private void logOptimizationResults() {
        optimizationLog.append("\n=== RISULTATI OTTIMIZZAZIONE ===\n");
        optimizationLog.append("Clausole originali: ").append(originalClauseCount).append("\n");
        optimizationLog.append("Clausole eliminate: ").append(eliminatedClauses).append("\n");
        optimizationLog.append("Clausole finali: ").append(originalClauseCount - eliminatedClauses).append("\n");

        if (originalClauseCount > 0) {
            double reductionPercentage = (double) eliminatedClauses / originalClauseCount * 100;
            optimizationLog.append("Riduzione: ").append(String.format("%.1f%%", reductionPercentage)).append("\n");
        }

        optimizationLog.append("===============================\n");

        LOGGER.info("Ottimizzazione sussunzione completata: " + eliminatedClauses + " clausole eliminate");
    }

    /**
     * Conversione sicura a stringa con gestione errori
     */
    private String safeToString(CNFConverter formula) {
        try {
            return formula != null ? formula.toString() : "null";
        } catch (Exception e) {
            LOGGER.log(Level.WARNING, "Errore toString() su formula", e);
            return "ERROR_IN_TOSTRING";
        }
    }

    //endregion

    //region INTERFACCIA PUBBLICA INFORMAZIONI

    /**
     * Restituisce informazioni dettagliate sull'ottimizzazione
     */
    public String getOptimizationInfo() {
        StringBuilder info = new StringBuilder();
        info.append("=== SUBSUMPTION OPTIMIZATION REPORT ===\n");
        info.append("Clausole originali: ").append(originalClauseCount).append("\n");
        info.append("Clausole eliminate: ").append(eliminatedClauses).append("\n");
        info.append("Clausole finali: ").append(originalClauseCount - eliminatedClauses).append("\n");

        if (originalClauseCount > 0) {
            double reductionPercentage = (double) eliminatedClauses / originalClauseCount * 100;
            info.append("Riduzione percentuale: ").append(String.format("%.1f%%", reductionPercentage)).append("\n");
        }

        info.append("\nDettagli ottimizzazione:\n");
        info.append(optimizationLog.toString());
        info.append("======================================\n");

        return info.toString();
    }

    /**
     * @return numero clausole eliminate
     */
    public int getEliminatedClausesCount() {
        return eliminatedClauses;
    }

    /**
     * @return numero clausole originali
     */
    public int getOriginalClausesCount() {
        return originalClauseCount;
    }

    /**
     * Reset per nuova ottimizzazione
     */
    public void reset() {
        resetState();
        LOGGER.fine("SubsumptionPrinciple resettato");
    }

    @Override
    public String toString() {
        return String.format("SubsumptionPrinciple[original=%d, eliminated=%d, final=%d]",
                originalClauseCount, eliminatedClauses, originalClauseCount - eliminatedClauses);
    }

    //endregion
}