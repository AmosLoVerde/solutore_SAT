package org.sat.cdcl;

import java.util.Map;

/**
 * Classe per rappresentare il risultato di una risoluzione SAT.
 * Reimplementata basandosi sul progetto X con output dettagliato simile.
 */
public class SATResult {

    /** Indica se la formula è soddisfacibile */
    private final boolean satisfiable;

    /** Assegnamento delle variabili (null se insoddisfacibile) */
    private final Map<String, Boolean> assignment;

    /** Prova di insoddisfacibilità (null se soddisfacibile) */
    private final String proof;

    /** Statistiche sulla risoluzione */
    private final SATStatistics statistics;

    /**
     * Costruttore per un risultato SAT con statistiche.
     */
    public SATResult(boolean satisfiable, Map<String, Boolean> assignment, String proof, SATStatistics statistics) {
        this.satisfiable = satisfiable;
        this.assignment = assignment;
        this.proof = proof;
        this.statistics = statistics != null ? statistics : new SATStatistics();

        // Validazione dell'input
        if (satisfiable && assignment == null) {
            throw new IllegalArgumentException("L'assegnamento non può essere null per risultati SAT");
        }
    }

    /**
     * Costruttore semplificato.
     */
    public SATResult(boolean satisfiable, Map<String, Boolean> assignment, String proof) {
        this(satisfiable, assignment, proof, new SATStatistics());
    }

    /**
     * Verifica se la formula è soddisfacibile.
     */
    public boolean isSatisfiable() {
        return satisfiable;
    }

    /**
     * Ottiene l'assegnamento delle variabili.
     */
    public Map<String, Boolean> getAssignment() {
        return assignment;
    }

    /**
     * Ottiene la prova di insoddisfacibilità.
     */
    public String getProof() {
        return proof;
    }

    /**
     * Ottiene le statistiche sulla risoluzione.
     */
    public SATStatistics getStatistics() {
        return statistics;
    }

    /**
     * Rappresentazione testuale del risultato in stile progetto X.
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        if (satisfiable) {
            sb.append("SAT\n");
            sb.append("Model:\n");

            if (assignment != null && !assignment.isEmpty()) {
                assignment.entrySet().stream()
                        .sorted(Map.Entry.comparingByKey())
                        .forEach(entry -> {
                            String varName = entry.getKey();
                            Boolean value = entry.getValue();
                            sb.append(varName).append(" -> ").append(value).append("\n");
                        });
            } else {
                sb.append("Nessun modello disponibile.\n");
            }
        } else {
            sb.append("UNSAT\n");

            if (proof != null && !proof.trim().isEmpty()) {
                // Controlla se la prova è troppo grande (come nel progetto X)
                if (statistics.getProofSize() > 0 && statistics.getProofSize() < 500) {
                    sb.append("The proof for unsat is:\n");
                    sb.append(proof);
                } else {
                    sb.append("The proof is too big, so it goes beyond the human understanding\n");
                }
            } else {
                sb.append("Nessuna prova dettagliata disponibile.\n");
            }
        }

        return sb.toString();
    }

    /**
     * Crea un risultato per una formula soddisfacibile.
     */
    public static SATResult satisfiable(Map<String, Boolean> assignment, SATStatistics statistics) {
        if (assignment == null) {
            throw new IllegalArgumentException("L'assegnamento non può essere null per risultati SAT");
        }
        return new SATResult(true, assignment, null, statistics);
    }

    /**
     * Crea un risultato per una formula insoddisfacibile.
     */
    public static SATResult unsatisfiable(String proof, SATStatistics statistics) {
        return new SATResult(false, null, proof, statistics);
    }
}

