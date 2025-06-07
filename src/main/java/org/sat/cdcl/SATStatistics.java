package org.sat.cdcl;

/**
 * STATISTICHE SAT - Sistema completo di raccolta e analisi metriche di esecuzione
 *
 * Raccoglie, elabora e presenta statistiche dettagliate durante la risoluzione SAT,
 * fornendo insights completi su performance, complessità algoritmica e resource usage.
 * Supporta analisi di efficienza e debugging avanzato per algoritmi CDCL.
 *
 * METRICHE PRINCIPALI TRACCIATA:
 * • Decisioni: Scelte euristiche durante la ricerca
 * • Conflitti: Conflitti rilevati e analizzati
 * • Propagazioni: Implicazioni derivate automaticamente
 * • Clausole apprese: Learning dinamico dalla conflict analysis
 * • Backjumps: Operazioni di backtracking non-cronologico
 * • Prove: Dimensioni e complessità prove generate
 * • Timing: Misurazione accurata tempi di esecuzione
 *
 * CARATTERISTICHE DESIGN:
 * • Thread-safe: Increment operations atomiche per concorrenza
 * • Performance-oriented: Overhead minimo durante raccolta
 * • Output professionale: Formati standard per reporting
 * • Analisi automatica: Calcolo ratios e trend significativi
 * • Debugging support: Informazioni dettagliate per troubleshooting
 *
 * FORMATI OUTPUT SUPPORTATI:
 * • Compact: Singola linea per logging rapido
 * • Detailed: Tabella formattata per analisi approfondita
 * • Academic: Compatible con benchmark e pubblicazioni
 * • Debug: Informazioni aggiuntive per sviluppo
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
     * Calcola throughput decisioni per secondo.
     * Metrica di performance per comparazione algoritmi.
     *
     * @return decisioni per secondo (0.0 se tempo non disponibile)
     */
    public double getDecisionsPerSecond() {
        long timeMs = getExecutionTimeMs();
        return timeMs > 0 ? (double) decisions * 1000 / timeMs : 0.0;
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
        return String.format("Stats[Dec:%d, Conf:%d, Prop:%d, Learn:%d, Time:%dms]",
                decisions, conflicts, propagations, learnedClauses, getExecutionTimeMs());
    }

    /**
     * Genera analisi avanzata con ratios e performance insights.
     * Utile per debugging e ottimizzazione algoritmi.
     *
     * @return stringa con analisi approfondita delle metriche
     */
    public String getAdvancedAnalysis() {
        StringBuilder analysis = new StringBuilder();

        analysis.append("=== ANALISI AVANZATA PERFORMANCE ===\n");
        analysis.append(String.format("Decisioni: %d\n", decisions));
        analysis.append(String.format("Conflitti: %d (%.2f per decisione)\n", conflicts, getConflictRate()));
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

    //endregion

    //region UTILITÀ E VALIDAZIONE

    /**
     * Verifica se le statistiche contengono dati significativi.
     * Utile per determinare se una risoluzione ha effettivamente lavorato.
     *
     * @return true se almeno una metrica core è stata registrata
     */
    public boolean hasSignificantData() {
        return decisions > 0 || conflicts > 0 || propagations > 0 || getExecutionTimeMs() > 0;
    }

    /**
     * Verifica integrità delle statistiche raccolte.
     * Controlla consistenza logica tra metriche correlate.
     *
     * @return true se statistiche sono logicamente consistenti
     */
    public boolean isConsistent() {
        // Verifiche di consistenza logica
        if (conflicts > decisions && decisions > 0) {
            return false; // Non può avere più conflitti che decisioni in scenari normali
        }

        if (learnedClauses > conflicts && conflicts > 0) {
            return false; // Non può imparare più clausole che conflitti avuti
        }

        if (executionTimeMs < 0) {
            return false; // Tempo negativo impossibile
        }

        return true;
    }

    /**
     * Reset completo di tutte le statistiche.
     * Utile per riutilizzo della stessa istanza su problemi diversi.
     */
    public void reset() {
        decisions = 0;
        propagations = 0;
        conflicts = 0;
        learnedClauses = 0;
        backjumps = 0;
        proofSize = 0;
        executionTimeMs = 0;
        startTime = System.currentTimeMillis();
        timerStopped = false;
    }

    /**
     * Copia le statistiche da un'altra istanza.
     * Utile per aggregazione o backup di statistiche.
     *
     * @param other istanza da cui copiare le statistiche
     * @throws IllegalArgumentException se other è null
     */
    public void copyFrom(SATStatistics other) {
        if (other == null) {
            throw new IllegalArgumentException("Istanza di copia non può essere null");
        }

        this.decisions = other.decisions;
        this.propagations = other.propagations;
        this.conflicts = other.conflicts;
        this.learnedClauses = other.learnedClauses;
        this.backjumps = other.backjumps;
        this.proofSize = other.proofSize;
        this.executionTimeMs = other.executionTimeMs;
        this.timerStopped = other.timerStopped;
        // Non copiamo startTime per preservare timing della istanza corrente
    }

    //endregion
}