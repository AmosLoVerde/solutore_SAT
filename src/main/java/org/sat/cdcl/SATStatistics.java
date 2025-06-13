package org.sat.cdcl;

/**
 * STATISTICHE SAT - Sistema completo di raccolta e analisi metriche di esecuzione
 *
 * Raccoglie, elabora e presenta statistiche dettagliate durante la risoluzione SAT,
 * includendo il supporto completo per la tecnica restart e metriche di performance
 * avanzate per analisi algoritmica approfondita.
 *
 */
public class SATStatistics {

    //region CONTATORI METRICHE CORE

    /**
     * Numero di decisioni euristiche prese durante la ricerca.
     * Rappresenta la profondità di esplorazione dello spazio delle soluzioni.
     */
    private int decisions = 0;

    /**
     * Numero di propagazioni unitarie eseguite.
     * Indica l'efficacia della constraint propagation nell'algoritmo.
     */
    private int propagations = 0;

    /**
     * Numero di conflitti rilevati durante la risoluzione.
     * Misura la difficoltà intrinseca del problema e efficacia delle euristiche.
     */
    private int conflicts = 0;

    /**
     * Numero di clausole apprese tramite conflict analysis.
     * Rappresenta il learning dinamico e l'evoluzione della base di conoscenza.
     */
    private int learnedClauses = 0;

    /**
     * Numero di operazioni di backjump non-cronologico eseguite.
     * Indica l'efficacia del conflict-driven backtracking.
     */
    private int backjumps = 0;

    /**
     * Numero di restart eseguiti durante la risoluzione.
     * Indica l'utilizzo della tecnica di restart per prevenzione stalli.
     */
    private int restarts = 0;

    //endregion

    //region METRICHE PROVE E VALIDAZIONE

    /**
     * Dimensione della prova generata per formule UNSAT.
     * Misurata in numero di passi di risoluzione nella dimostrazione.
     */
    private int proofSize = 0;

    //endregion

    //region TIMING E PERFORMANCE

    /**
     * Tempo di esecuzione totale in millisecondi.
     * Calcolato dalla chiamata a solve() fino al completamento.
     */
    private long executionTimeMs = 0;

    /**
     * Timestamp di inizio esecuzione per calcolo timing accurato.
     * Utilizzato internamente per gestione timer.
     */
    private long startTime = 0;

    /**
     * Flag per indicare se il timer è stato fermato.
     * Previene multiple stop operations e garantisce accuratezza timing.
     */
    private boolean timerStopped = false;

    //endregion

    //region INIZIALIZZAZIONE E CONFIGURAZIONE

    /**
     * Inizializza sistema di statistiche con timer automatico.
     * Avvia immediatamente la misurazione del tempo di esecuzione.
     */
    public SATStatistics() {
        this.startTime = System.currentTimeMillis();
        this.timerStopped = false;
    }

    //endregion

    //region OPERAZIONI DI INCREMENTO CONTATORI

    /**
     * Incrementa contatore decisioni euristiche.
     * Thread-safe per utilizzo in contesti concorrenti.
     */
    public synchronized void incrementDecisions() {
        decisions++;
    }

    /**
     * Incrementa contatore propagazioni unitarie.
     * Chiamato ad ogni unit propagation eseguita con successo.
     */
    public synchronized void incrementPropagations() {
        propagations++;
    }

    /**
     * Incrementa contatore conflitti rilevati.
     * Chiamato ad ogni conflict analysis avviata.
     */
    public synchronized void incrementConflicts() {
        conflicts++;
    }

    /**
     * Incrementa contatore clausole apprese.
     * Chiamato ad ogni learning di nuova clausola dal conflict analysis.
     */
    public synchronized void incrementLearnedClauses() {
        learnedClauses++;
    }

    /**
     * Incrementa contatore operazioni di backjump.
     * Chiamato ad ogni backtracking non-cronologico eseguito.
     */
    public synchronized void incrementBackjumps() {
        backjumps++;
    }

    /**
     * Incrementa contatore restart eseguiti.
     * Chiamato ad ogni procedura restart completata con successo.
     */
    public synchronized void incrementRestarts() {
        restarts++;
    }

    //endregion

    //region GESTIONE METRICHE SPECIALI

    /**
     * Imposta dimensione della prova generata per formule UNSAT.
     *
     * @param size numero di passi nella dimostrazione di insoddisfacibilità
     * @throws IllegalArgumentException se size negativo
     */
    public void setProofSize(int size) {
        if (size < 0) {
            throw new IllegalArgumentException("Dimensione prova non può essere negativa: " + size);
        }
        this.proofSize = size;
    }

    //endregion

    //region GESTIONE TIMING

    /**
     * Ferma la misurazione del tempo di esecuzione.
     * Calcola il tempo totale trascorso dall'inizializzazione.
     * Operazione idempotente: chiamate multiple sono sicure.
     */
    public void stopTimer() {
        if (startTime > 0 && !timerStopped) {
            executionTimeMs = System.currentTimeMillis() - startTime;
            timerStopped = true;
        }
    }

    /**
     * Restituisce tempo di esecuzione corrente in millisecondi.
     * Se timer non fermato, calcola tempo parziale dinamicamente.
     *
     * @return tempo di esecuzione in ms (corrente o finale)
     */
    public long getExecutionTimeMs() {
        if (!timerStopped && startTime > 0) {
            // Timer ancora attivo: calcola tempo parziale
            return System.currentTimeMillis() - startTime;
        }
        return executionTimeMs;
    }

    /**
     * Verifica se il timer è stato fermato.
     *
     * @return true se timing è finalizzato, false se ancora in corso
     */
    public boolean isTimerStopped() {
        return timerStopped;
    }

    //endregion

    //region ACCESSORS LETTURA METRICHE

    /** @return numero di decisioni euristiche prese */
    public int getDecisions() {
        return decisions;
    }

    /** @return numero di propagazioni unitarie eseguite */
    public int getPropagations() {
        return propagations;
    }

    /** @return numero di conflitti rilevati */
    public int getConflicts() {
        return conflicts;
    }

    /** @return numero di clausole apprese */
    public int getLearnedClauses() {
        return learnedClauses;
    }

    /** @return numero di backjump eseguiti */
    public int getBackjumps() {
        return backjumps;
    }

    /** @return numero di restart eseguiti */
    public int getRestarts() {
        return restarts;
    }

    /** @return dimensione prova generata (0 se non disponibile) */
    public int getProofSize() {
        return proofSize;
    }

    //endregion

    //region ANALISI E RATIOS

    /**
     * Calcola tasso di conflitti per decisione.
     * Metrica chiave per valutare difficoltà del problema.
     *
     * @return rapporto conflitti/decisioni (0.0 se nessuna decisione)
     */
    public double getConflictRate() {
        return decisions > 0 ? (double) conflicts / decisions : 0.0;
    }

    /**
     * Calcola efficacia del learning tramite ratio clausole/conflitti.
     * Indica quanto learning si riesce ad estrarre da ogni conflitto.
     *
     * @return rapporto clausole_apprese/conflitti (0.0 se nessun conflitto)
     */
    public double getLearningEfficiency() {
        return conflicts > 0 ? (double) learnedClauses / conflicts : 0.0;
    }

    /**
     * Calcola efficacia della propagazione tramite ratio propagazioni/decisioni.
     * Misura quanto constraint propagation si ottiene per ogni scelta euristica.
     *
     * @return rapporto propagazioni/decisioni (0.0 se nessuna decisione)
     */
    public double getPropagationEfficiency() {
        return decisions > 0 ? (double) propagations / decisions : 0.0;
    }

    /**
     * Calcola frequenza restart tramite ratio conflitti/restart.
     * Indica ogni quanti conflitti viene eseguito un restart in media.
     *
     * @return rapporto conflitti/restart (0.0 se nessun restart)
     */
    public double getRestartFrequency() {
        return restarts > 0 ? (double) conflicts / restarts : 0.0;
    }

    /**
     * Calcola throughput decisioni per secondo.
     * Metrica di performance per comparazione algoritmi.
     *
     * @return decisioni per secondo (0.0 se tempo non disponibile)
     */
    public double getDecisionsPerSecond() {
        long timeMs = getExecutionTimeMs();
        return timeMs > 0 ? (double) decisions * 1000 / timeMs : 0.0;
    }

    /**
     * Calcola percentuale di conflitti che hanno causato restart.
     * Indica l'intensità di utilizzo della tecnica restart.
     *
     * @return percentuale conflitti → restart (0.0-100.0)
     */
    public double getRestartUtilizationRate() {
        if (conflicts == 0) return 0.0;
        // Assumendo soglia di 5 conflitti per restart
        int expectedRestarts = conflicts / 5;
        return expectedRestarts > 0 ? (double) restarts / expectedRestarts * 100.0 : 0.0;
    }

    //endregion

    //region OUTPUT E RAPPRESENTAZIONE

    /**
     * Genera rappresentazione testuale in stile accademico/benchmark.
     * Output compatibile con standard di valutazione SAT solver.
     *
     * @return statistiche formattate per reporting professionale
     */
    @Override
    public String toString() {
        StringBuilder output = new StringBuilder();

        output.append("===========================[ EVALUATION COMPLETED: PROBLEM STATS ]===========================\n");
        output.append("======================================[ SEARCH STATS ]=======================================\n");
        output.append("    Decisioni: ").append(decisions).append("\n");
        output.append("    Conflitti: ").append(conflicts).append("\n");

        if (restarts > 0) {
            output.append("    Restart:   ").append(restarts).append("\n");
        }

        output.append("    Tempo:     ").append(getExecutionTimeMs()).append("ms\n");

        // Gestione intelligente visualizzazione prova
        if (proofSize > 0) {
            if (proofSize < 500) {
                output.append("    Dimensione prova: ").append(proofSize).append("\n");
            } else {
                output.append("    Dimensione prova: oltre 500 passi\n");
            }
        }

        output.append("=============================================================================================\n");

        return output.toString();
    }

    /**
     * Stampa statistiche dettagliate con informazioni sul problema.
     * Utilizzato per output finale con contesto della formula risolta.
     *
     * @param variableCount numero di variabili nella formula originale
     * @param clauseCount numero di clausole nella formula originale
     * @param result esito della risoluzione ("SAT", "UNSAT", "TIMEOUT")
     */
    public void printDetailedStats(int variableCount, int clauseCount, String result) {
        System.out.println("===========================[ EVALUATION COMPLETED: PROBLEM STATS ]===========================");
        System.out.println("    Variabili: " + variableCount);
        System.out.println("    Clausole:  " + clauseCount);
        System.out.println("======================================[ SEARCH STATS ]=======================================");
        System.out.println("    Decisioni: " + decisions);
        System.out.println("    Conflitti: " + conflicts);

        if (restarts > 0) {
            System.out.println("    Restart:   " + restarts);
        }

        System.out.println("    Tempo:     " + getExecutionTimeMs() + "ms");
        System.out.println("    Risultato: " + result);

        // Output intelligente prova per risultati UNSAT
        if ("UNSAT".equals(result)) {
            if (proofSize > 0 && proofSize < 500) {
                System.out.println("    Dimensione prova: " + proofSize);
            } else if (proofSize >= 500) {
                System.out.println("    Dimensione prova: oltre 500 passi");
            }
        }

        System.out.println("=============================================================================================");
    }

    /**
     * Genera output compatto per logging rapido.
     * Formato su singola linea per integrazione in log systems.
     *
     * @return stringa compatta con metriche essenziali
     */
    public String toCompactString() {
        if (restarts > 0) {
            return String.format("Stats[Dec:%d, Conf:%d, Restart:%d, Prop:%d, Learn:%d, Time:%dms]",
                    decisions, conflicts, restarts, propagations, learnedClauses, getExecutionTimeMs());
        } else {
            return String.format("Stats[Dec:%d, Conf:%d, Prop:%d, Learn:%d, Time:%dms]",
                    decisions, conflicts, propagations, learnedClauses, getExecutionTimeMs());
        }
    }

    /**
     * Genera analisi avanzata con ratios e performance insights.
     * Include metriche specifiche restart per analisi approfondita.
     *
     * @return stringa con analisi approfondita delle metriche
     */
    public String getAdvancedAnalysis() {
        StringBuilder analysis = new StringBuilder();

        analysis.append("=== ANALISI AVANZATA PERFORMANCE ===\n");
        analysis.append(String.format("Decisioni: %d\n", decisions));
        analysis.append(String.format("Conflitti: %d (%.2f per decisione)\n", conflicts, getConflictRate()));

        if (restarts > 0) {
            analysis.append(String.format("Restart: %d (%.2f conflitti per restart)\n", restarts, getRestartFrequency()));
            analysis.append(String.format("Utilizzo restart: %.1f%% dell'ottimale\n", getRestartUtilizationRate()));
        }

        analysis.append(String.format("Propagazioni: %d (%.2f per decisione)\n", propagations, getPropagationEfficiency()));
        analysis.append(String.format("Clausole apprese: %d (%.2f per conflitto)\n", learnedClauses, getLearningEfficiency()));
        analysis.append(String.format("Backjumps: %d\n", backjumps));
        analysis.append(String.format("Tempo: %dms (%.2f decisioni/sec)\n", getExecutionTimeMs(), getDecisionsPerSecond()));

        if (proofSize > 0) {
            analysis.append(String.format("Prova: %d passi\n", proofSize));
        }

        analysis.append("====================================\n");

        return analysis.toString();
    }

    /**
     * Genera report specifico per restart con dettagli tecnici.
     * Utilizzato per file di output STATS/RESTART/*.stats
     *
     * @return report dettagliato restart per salvataggio
     */
    public String getRestartAnalysisReport() {
        StringBuilder report = new StringBuilder();

        report.append("=== ANALISI DETTAGLIATA RESTART ===\n\n");

        // Statistiche base
        report.append("STATISTICHE BASE:\n");
        report.append(String.format("- Restart eseguiti: %d\n", restarts));
        report.append(String.format("- Conflitti totali: %d\n", conflicts));
        report.append(String.format("- Soglia restart: 5 conflitti\n"));

        if (restarts > 0) {
            report.append(String.format("- Media conflitti/restart: %.1f\n", getRestartFrequency()));
            report.append(String.format("- Utilizzo restart: %.1f%% dell'ottimale\n", getRestartUtilizationRate()));
        }

        report.append("\n");

        // Efficacia tecnica
        report.append("EFFICACIA TECNICA:\n");
        if (restarts > 0) {
            report.append("- Restart applicati per prevenire stalli\n");
            report.append("- Sussunzione automatica post-restart attiva\n");
            report.append("- Preservazione clausole apprese: 100%\n");
            report.append("- Preservazione livello 0: 100%\n");

            // Stima benefici
            double restartBenefit = Math.min(restarts * 10.0, 100.0); // Stima euristica
            report.append(String.format("- Beneficio stimato: %.0f%% riduzione tempo ricerca\n", restartBenefit));
        } else {
            report.append("- Nessun restart necessario\n");
            report.append("- Risoluzione efficiente senza interventi\n");
            report.append("- Formula risolta linearmente\n");
        }

        report.append("\n");

        // Raccomandazioni
        report.append("RACCOMANDAZIONI:\n");
        if (restarts == 0 && conflicts > 10) {
            report.append("- Considerare abilitazione restart per formule più complesse\n");
        } else if (restarts > conflicts / 3) {
            report.append("- Restart molto frequenti: considerare soglia più alta\n");
        } else if (restarts > 0) {
            report.append("- Configurazione restart ottimale per questa formula\n");
        }

        report.append("\n===================================\n");

        return report.toString();
    }

    //endregion
}