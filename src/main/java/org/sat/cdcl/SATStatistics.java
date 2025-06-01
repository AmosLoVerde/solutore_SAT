package org.sat.cdcl;

/**
 * Classe per raccogliere statistiche durante la risoluzione SAT.
 * Basata sul progetto X con output in stile "EVALUATION COMPLETED".
 */
public class SATStatistics {

    /** Numero di decisioni prese */
    private int decisions = 0;

    /** Numero di propagazioni */
    private int propagations = 0;

    /** Numero di conflitti rilevati */
    private int conflicts = 0;

    /** Numero di clausole apprese */
    private int learnedClauses = 0;

    /** Numero di backjump effettuati */
    private int backjumps = 0;

    /** Dimensione della prova (per controllo output) */
    private int proofSize = 0;

    /** Tempo di esecuzione in millisecondi */
    private long executionTimeMs = 0;

    /** Tempo di inizio della risoluzione */
    private long startTime = 0;

    /** Flag per indicare se il timer è stato fermato */
    private boolean timerStopped = false;

    /**
     * Costruttore delle statistiche.
     */
    public SATStatistics() {
        this.startTime = System.currentTimeMillis();
    }

    /**
     * Incrementa il contatore delle decisioni.
     */
    public void incrementDecisions() {
        decisions++;
    }

    /**
     * Incrementa il contatore delle propagazioni.
     */
    public void incrementPropagations() {
        propagations++;
    }

    /**
     * Incrementa il contatore dei conflitti.
     */
    public void incrementConflicts() {
        conflicts++;
    }

    /**
     * Incrementa il contatore delle clausole apprese.
     */
    public void incrementLearnedClauses() {
        learnedClauses++;
    }

    /**
     * Incrementa il contatore dei backjump.
     */
    public void incrementBackjumps() {
        backjumps++;
    }

    /**
     * Imposta la dimensione della prova.
     */
    public void setProofSize(int size) {
        this.proofSize = size;
    }

    /**
     * Termina la misurazione del tempo di esecuzione.
     */
    public void stopTimer() {
        if (startTime > 0 && !timerStopped) {
            executionTimeMs = System.currentTimeMillis() - startTime;
            timerStopped = true;
        }
    }

    // Getters
    public int getDecisions() { return decisions; }
    public int getPropagations() { return propagations; }
    public int getConflicts() { return conflicts; }
    public int getLearnedClauses() { return learnedClauses; }
    public int getBackjumps() { return backjumps; }
    public int getProofSize() { return proofSize; }
    public long getExecutionTimeMs() {
        if (!timerStopped && startTime > 0) {
            return System.currentTimeMillis() - startTime;
        }
        return executionTimeMs;
    }

    /**
     * Output statistiche in stile progetto X.
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append("===========================[ EVALUATION COMPLETED: PROBLEM STATS ]===========================\n");
        // Note: Variables e Clauses verranno aggiunte dal chiamante se necessario
        sb.append("======================================[ SEARCH STATS ]=======================================\n");
        sb.append("    Decisions: ").append(decisions).append("\n");
        sb.append("    Conflicts: ").append(conflicts).append("\n");
        sb.append("    Time:      ").append(getExecutionTimeMs()).append("ms\n");

        if (proofSize > 0) {
            if (proofSize < 500) {
                sb.append("    Proof size: ").append(proofSize).append("\n");
            } else {
                sb.append("    Proof size: over 500\n");
            }
        }

        sb.append("=============================================================================================\n");

        return sb.toString();
    }

    /**
     * Stampa statistiche complete (metodo di utilità).
     */
    public void printDetailedStats(int variableCount, int clauseCount, String result) {
        System.out.println("===========================[ EVALUATION COMPLETED: PROBLEM STATS ]===========================");
        System.out.println("    Variables: " + variableCount);
        System.out.println("    Clauses:   " + clauseCount);
        System.out.println("======================================[ SEARCH STATS ]=======================================");
        System.out.println("    Decisions: " + decisions);
        System.out.println("    Conflicts: " + conflicts);
        System.out.println("    Time:      " + getExecutionTimeMs() + "ms");
        System.out.println("    Result:    " + result);

        if ("UNSAT".equals(result)) {
            if (proofSize < 500) {
                System.out.println("    Proof size: " + proofSize);
            } else {
                System.out.println("    Proof size: over 500");
            }
        }

        System.out.println("=============================================================================================");
    }
}
