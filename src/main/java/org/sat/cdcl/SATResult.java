package org.sat.cdcl;

import java.util.Map;
import java.util.Objects;

/**
 * RISULTATO SAT - Contenitore immutabile per esiti di risoluzione booleana
 *
 * Rappresenta il risultato completo di una risoluzione SAT con accesso unificato
 * a tutti i dati prodotti dall'algoritmo CDCL: modello, prove, statistiche.
 *
 * DESIGN PRINCIPLES:
 * • Immutabilità garantita per thread-safety
 * • Factory methods per costruzione type-safe
 * • Validazione rigorosa per consistenza logica
 * • Output professionale per reporting
 *
 * COMPONENTI:
 * • Esito: SAT (soddisfacibile) vs UNSAT (insoddisfacibile)
 * • Modello: Assegnamento variabili per formule SAT
 * • Prova: Dimostrazione matematica per formule UNSAT
 * • Statistiche: Metriche performance e complessità
 *
 */
public class SATResult {

    //region ATTRIBUTI CORE

    /**
     * Indica se la formula è soddisfacibile.
     * true = SAT (esiste modello), false = UNSAT (nessun modello possibile)
     */
    private final boolean satisfiable;

    /**
     * Assegnamento completo variabili per formule SAT.
     * Non null per SAT, null per UNSAT.
     */
    private final Map<String, Boolean> assignment;

    /**
     * Prova matematica di insoddisfacibilità per formule UNSAT.
     * Non null per UNSAT, null per SAT.
     */
    private final String proof;

    /**
     * Statistiche dettagliate di esecuzione dell'algoritmo CDCL.
     * Sempre disponibili per tracciabilità completa.
     */
    private final SATStatistics statistics;

    //endregion

    //region COSTRUZIONE E VALIDAZIONE

    /**
     * Costruisce risultato SAT con validazione completa dei parametri.
     *
     * VALIDAZIONI:
     * • Consistenza logica: satisfiable ↔ (assignment != null)
     * • Esclusività: modello e prova mutuamente esclusivi
     * • Completezza: assignment non vuoto per SAT
     *
     * @param satisfiable true se formula soddisfacibile
     * @param assignment modello variabili (richiesto per SAT, null per UNSAT)
     * @param proof prova insoddisfacibilità (richiesta per UNSAT, null per SAT)
     * @param statistics metriche esecuzione (null → default inizializzato)
     * @throws IllegalArgumentException se parametri inconsistenti
     */
    public SATResult(boolean satisfiable, Map<String, Boolean> assignment, String proof, SATStatistics statistics) {
        validateParameterConsistency(satisfiable, assignment, proof);

        this.satisfiable = satisfiable;
        this.assignment = assignment;
        this.proof = proof;
        this.statistics = statistics != null ? statistics : new SATStatistics();

        validateConstructedState();
    }

    /**
     * Costruttore semplificato senza statistiche esplicite.
     * Utile quando statistiche non sono immediatamente disponibili.
     */
    public SATResult(boolean satisfiable, Map<String, Boolean> assignment, String proof) {
        this(satisfiable, assignment, proof, new SATStatistics());
    }

    /**
     * Valida consistenza logica tra parametri di costruzione.
     */
    private void validateParameterConsistency(boolean satisfiable, Map<String, Boolean> assignment, String proof) {
        if (satisfiable) {
            // Formula SAT: richiede modello, prova deve essere null
            if (assignment == null || assignment.isEmpty()) {
                throw new IllegalArgumentException("Risultato SAT richiede assegnamento variabili non vuoto");
            }
            if (proof != null && !proof.trim().isEmpty()) {
                throw new IllegalArgumentException("Risultato SAT non può avere prova insoddisfacibilità");
            }
        } else {
            // Formula UNSAT: richiede prova, modello deve essere null
            if (assignment != null) {
                throw new IllegalArgumentException("Risultato UNSAT non può avere assegnamento variabili");
            }
        }
    }

    /**
     * Valida stato interno dopo costruzione per robustezza.
     */
    private void validateConstructedState() {
        if (assignment != null) {
            try {
                assignment.size(); // Test accesso per validazione struttura
            } catch (Exception e) {
                throw new IllegalArgumentException("Assignment map malformato", e);
            }
        }

        if (statistics == null) {
            throw new IllegalStateException("Statistiche non inizializzate correttamente");
        }
    }

    //endregion

    //region FACTORY METHODS TYPE-SAFE

    /**
     * Crea risultato SAT con modello e statistiche.
     * Factory method type-safe per costruzione risultati soddisfacibili.
     *
     * @param assignment modello completo delle variabili (non null, non vuoto)
     * @param statistics metriche di esecuzione
     * @return risultato SAT validato
     * @throws IllegalArgumentException se assignment null o vuoto
     */
    public static SATResult satisfiable(Map<String, Boolean> assignment, SATStatistics statistics) {
        if (assignment == null || assignment.isEmpty()) {
            throw new IllegalArgumentException("Modello SAT non può essere null o vuoto");
        }
        return new SATResult(true, assignment, null, statistics);
    }

    /**
     * Crea risultato UNSAT con prova e statistiche.
     * Factory method type-safe per costruzione risultati insoddisfacibili.
     *
     * @param proof dimostrazione matematica di insoddisfacibilità
     * @param statistics metriche di esecuzione
     * @return risultato UNSAT validato
     */
    public static SATResult unsatisfiable(String proof, SATStatistics statistics) {
        return new SATResult(false, null, proof, statistics);
    }

    /**
     * Crea risultato SAT con solo modello (statistiche default).
     */
    public static SATResult satisfiable(Map<String, Boolean> assignment) {
        return satisfiable(assignment, new SATStatistics());
    }

    /**
     * Crea risultato UNSAT con solo prova (statistiche default).
     */
    public static SATResult unsatisfiable(String proof) {
        return unsatisfiable(proof, new SATStatistics());
    }

    //endregion

    //region ACCESSORS E QUERY

    /**
     * Verifica se la formula è soddisfacibile.
     */
    public boolean isSatisfiable() {
        return satisfiable;
    }

    /**
     * Verifica se la formula è insoddisfacibile.
     */
    public boolean isUnsatisfiable() {
        return !satisfiable;
    }

    /**
     * Restituisce modello delle variabili per formule SAT.
     * @return mappa nome_variabile → valore per SAT, null per UNSAT
     */
    public Map<String, Boolean> getAssignment() {
        return assignment;
    }

    /**
     * Restituisce prova di insoddisfacibilità per formule UNSAT.
     * @return stringa prova matematica per UNSAT, null per SAT
     */
    public String getProof() {
        return proof;
    }

    /**
     * Restituisce statistiche complete di esecuzione.
     * @return metriche dettagliate sempre disponibili
     */
    public SATStatistics getStatistics() {
        return statistics;
    }

    /**
     * Verifica disponibilità modello soddisfacente.
     */
    public boolean hasModel() {
        return assignment != null && !assignment.isEmpty();
    }

    /**
     * Verifica disponibilità prova di insoddisfacibilità.
     */
    public boolean hasProof() {
        return proof != null && !proof.trim().isEmpty();
    }

    /**
     * Conta numero di variabili nel modello SAT.
     */
    public int getModelSize() {
        return assignment != null ? assignment.size() : 0;
    }

    /**
     * Verifica se il risultato è completo (SAT con modello O UNSAT con prova).
     */
    public boolean isComplete() {
        return (satisfiable && hasModel()) || (!satisfiable && hasProof());
    }

    //endregion

    //region OUTPUT E RAPPRESENTAZIONE

    /**
     * Genera rappresentazione testuale completa per output utente.
     * Formato professionale compatibile con standard accademici.
     *
     * STRUTTURA:
     * • Header con esito (SAT/UNSAT)
     * • Contenuto principale (modello o prova)
     * • Gestione intelligente dimensioni per leggibilità
     */
    @Override
    public String toString() {
        StringBuilder output = new StringBuilder();

        if (satisfiable) {
            output.append(generateSATOutput());
        } else {
            output.append(generateUNSATOutput());
        }

        return output.toString();
    }

    /**
     * Genera output formattato per risultati SAT con modello.
     */
    private String generateSATOutput() {
        StringBuilder satOutput = new StringBuilder();
        satOutput.append("SAT\n");
        satOutput.append("Modello:\n");

        if (hasModel()) {
            assignment.entrySet().stream()
                    .sorted(Map.Entry.comparingByKey())
                    .forEach(entry -> satOutput.append(entry.getKey())
                            .append(" → ").append(entry.getValue()).append("\n"));
        } else {
            satOutput.append("Errore: modello non disponibile per risultato SAT.\n");
        }

        return satOutput.toString();
    }

    /**
     * Genera output formattato per risultati UNSAT con prova.
     */
    private String generateUNSATOutput() {
        StringBuilder unsatOutput = new StringBuilder();
        unsatOutput.append("UNSAT\n");

        if (hasProof()) {
            if (shouldDisplayFullProof()) {
                unsatOutput.append("Prova di insoddisfacibilità:\n");
                unsatOutput.append(proof);
            } else {
                unsatOutput.append("Prova troppo grande per visualizzazione completa.\n");
                unsatOutput.append("Dimensione prova: ").append(statistics.getProofSize()).append(" passi.\n");
            }
        } else {
            unsatOutput.append("Prova di insoddisfacibilità non disponibile.\n");
        }

        return unsatOutput.toString();
    }

    /**
     * Determina se visualizzare prova completa basandosi su dimensioni ragionevoli.
     */
    private boolean shouldDisplayFullProof() {
        return statistics.getProofSize() > 0 &&
                statistics.getProofSize() < 500 &&
                proof.length() < 10000;
    }

    /**
     * Genera rappresentazione compatta per logging rapido.
     * @return stringa sintetica con informazioni essenziali
     */
    public String toCompactString() {
        return String.format("SATResult{%s, vars=%d, time=%dms}",
                satisfiable ? "SAT" : "UNSAT",
                getModelSize(),
                statistics.getExecutionTimeMs());
    }

    /**
     * Estrae riepilogo esecuzione per reporting rapido.
     */
    public String getExecutionSummary() {
        return String.format("Esito: %s | Decisioni: %d | Conflitti: %d | Tempo: %dms",
                satisfiable ? "SAT" : "UNSAT",
                statistics.getDecisions(),
                statistics.getConflicts(),
                statistics.getExecutionTimeMs());
    }

    //endregion

    //region UGUAGLIANZA E VALIDAZIONE

    /**
     * Uguaglianza basata su contenuto logico (esito, modello/prova).
     * Ignora statistiche per focus su equivalenza matematica.
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;

        SATResult other = (SATResult) obj;
        return satisfiable == other.satisfiable &&
                Objects.equals(assignment, other.assignment) &&
                Objects.equals(proof, other.proof);
    }

    /**
     * Hash code consistente con equals per utilizzo in collezioni.
     */
    @Override
    public int hashCode() {
        return Objects.hash(satisfiable, assignment, proof);
    }

    /**
     * Verifica se il risultato ha statistiche significative.
     */
    public boolean hasSignificantStatistics() {
        return statistics.getDecisions() > 0 ||
                statistics.getConflicts() > 0 ||
                statistics.getExecutionTimeMs() > 0;
    }

    /**
     * Verifica qualità del risultato per validazione completa.
     * @return true se risultato è ben formato e completo
     */
    public boolean isWellFormed() {
        try {
            // Validazione consistenza base
            if (satisfiable && !hasModel()) return false;
            if (!satisfiable && !hasProof()) return false;

            // Validazione contenuto modello se presente
            if (assignment != null) {
                for (Map.Entry<String, Boolean> entry : assignment.entrySet()) {
                    if (entry.getKey() == null || entry.getKey().trim().isEmpty()) return false;
                    if (entry.getValue() == null) return false;
                }
            }

            // Validazione contenuto prova se presente
            if (proof != null && proof.trim().isEmpty()) return false;

            return true;
        } catch (Exception e) {
            return false; // Qualsiasi eccezione indica malformazione
        }
    }

    //endregion
}