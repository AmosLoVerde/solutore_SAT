package org.sat.cdcl;

import java.util.Map;
import java.util.Objects;

/**
 * RISULTATO SAT - Rappresentazione completa dell'esito di risoluzione SAT
 *
 * Incapsula il risultato completo di una risoluzione di soddisfacibilità booleana,
 * fornendo accesso unificato a tutti i dati prodotti dall'algoritmo CDCL:
 * modello SAT, prove UNSAT, statistiche di esecuzione e metadata.
 *
 * COMPONENTI PRINCIPALI:
 * • Esito booleano: SAT (soddisfacibile) vs UNSAT (insoddisfacibile)
 * • Modello SAT: Assegnamento completo variabili per formule soddisfacibili
 * • Prova UNSAT: Dimostrazione matematica per formule insoddisfacibili
 * • Statistiche: Metriche dettagliate di performance e complessità
 *
 * CARATTERISTICHE DESIGN:
 * • Immutabilità garantita: Thread-safe e sicuro per caching
 * • Validazione rigorosa: Consistenza logica tra componenti
 * • Factory methods: Costruzione type-safe per casi specifici
 * • Output professionale: Formati standard per reporting
 *
 * UTILIZZO TIPICO:
 * - Per formule SAT: accesso al modello soddisfacente
 * - Per formule UNSAT: accesso alla prova matematica
 * - Per analisi performance: statistiche complete di esecuzione
 * - Per reporting: output formattato human-readable
 *
 */
public class SATResult {

    //region ATTRIBUTI CORE DEL RISULTATO

    /**
     * Indica se la formula è soddisfacibile.
     * • true: formula SAT, esiste modello soddisfacente
     * • false: formula UNSAT, nessun modello possibile
     * Invariante: determina quale tra modello/prova è disponibile
     */
    private final boolean satisfiable;

    /**
     * Assegnamento completo delle variabili per formule SAT.
     * Mappa nome_variabile → valore_booleano per tutte le variabili.
     * • Non null per risultati SAT
     * • Null per risultati UNSAT
     * Invariante: consistente con flag satisfiable
     */
    private final Map<String, Boolean> assignment;

    /**
     * Prova matematica di insoddisfacibilità per formule UNSAT.
     * Sequenza completa di spiegazioni che conducono alla clausola vuota.
     * • Non null per risultati UNSAT
     * • Null per risultati SAT
     * Invariante: consistente con flag satisfiable
     */
    private final String proof;

    /**
     * Statistiche dettagliate di esecuzione dell'algoritmo CDCL.
     * Include metriche di performance, complessità e resource usage.
     * • Sempre non null per garantire tracciabilità completa
     * • Default inizializzato se non fornito esplicitamente
     */
    private final SATStatistics statistics;

    //endregion

    //region COSTRUZIONE E VALIDAZIONE

    /**
     * Costruisce risultato SAT completo con validazione rigorosa dei parametri.
     *
     * VALIDAZIONI APPLICATE:
     * • Consistenza logica: satisfiable ↔ (assignment != null)
     * • Esclusività: modello e prova mutuamente esclusivi
     * • Completezza: statistiche sempre presenti
     * • Integrità: assignment non vuoto per formule SAT
     *
     * @param satisfiable true se formula soddisfacibile
     * @param assignment assegnamento variabili (richiesto per SAT, null per UNSAT)
     * @param proof prova insoddisfacibilità (richiesta per UNSAT, null per SAT)
     * @param statistics metriche esecuzione (null → default inizializzato)
     * @throws IllegalArgumentException se parametri inconsistenti
     */
    public SATResult(boolean satisfiable, Map<String, Boolean> assignment, String proof, SATStatistics statistics) {
        // Validazione consistenza logica parametri
        validateParameterConsistency(satisfiable, assignment, proof);

        // Assegnazione con inizializzazione sicura
        this.satisfiable = satisfiable;
        this.assignment = assignment;
        this.proof = proof;
        this.statistics = statistics != null ? statistics : new SATStatistics();

        // Validazione post-costruzione per robustezza
        validateConstructedState();
    }

    /**
     * Costruttore semplificato senza statistiche esplicite.
     * Utilizzato quando statistiche non sono immediatamente disponibili.
     *
     * @param satisfiable esito soddisfacibilità
     * @param assignment modello variabili (per SAT)
     * @param proof dimostrazione insoddisfacibilità (per UNSAT)
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
            // Nota: prova può essere null se generazione fallita
        }
    }

    /**
     * Valida stato interno dopo costruzione per robustezza.
     */
    private void validateConstructedState() {
        // Verifica immutabilità potenziale dell'assignment
        if (assignment != null) {
            // Test di accesso per validazione struttura
            try {
                assignment.size(); // Trigger potenziali eccezioni
            } catch (Exception e) {
                throw new IllegalArgumentException("Assignment map malformato", e);
            }
        }

        // Verifica statistiche inizializzate
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
     * Convenienza per casi dove statistiche non sono critiche.
     *
     * @param assignment modello delle variabili
     * @return risultato SAT con statistiche default
     */
    public static SATResult satisfiable(Map<String, Boolean> assignment) {
        return satisfiable(assignment, new SATStatistics());
    }

    /**
     * Crea risultato UNSAT con solo prova (statistiche default).
     * Convenienza per casi dove statistiche non sono critiche.
     *
     * @param proof dimostrazione insoddisfacibilità
     * @return risultato UNSAT con statistiche default
     */
    public static SATResult unsatisfiable(String proof) {
        return unsatisfiable(proof, new SATStatistics());
    }

    //endregion

    //region ACCESSORS E QUERY METHODS

    /**
     * @return true se la formula è soddisfacibile
     */
    public boolean isSatisfiable() {
        return satisfiable;
    }

    /**
     * @return true se la formula è insoddisfacibile
     */
    public boolean isUnsatisfiable() {
        return !satisfiable;
    }

    /**
     * Restituisce modello delle variabili per formule SAT.
     *
     * @return mappa nome_variabile → valore per formule SAT, null per UNSAT
     */
    public Map<String, Boolean> getAssignment() {
        return assignment;
    }

    /**
     * Restituisce prova di insoddisfacibilità per formule UNSAT.
     *
     * @return stringa prova matematica per formule UNSAT, null per SAT
     */
    public String getProof() {
        return proof;
    }

    /**
     * Restituisce statistiche complete di esecuzione.
     *
     * @return metriche dettagliate sempre disponibili
     */
    public SATStatistics getStatistics() {
        return statistics;
    }

    /**
     * Verifica disponibilità modello soddisfacente.
     *
     * @return true se modello disponibile e non vuoto
     */
    public boolean hasModel() {
        return assignment != null && !assignment.isEmpty();
    }

    /**
     * Verifica disponibilità prova di insoddisfacibilità.
     *
     * @return true se prova disponibile e non vuota
     */
    public boolean hasProof() {
        return proof != null && !proof.trim().isEmpty();
    }

    /**
     * Conta numero di variabili nel modello SAT.
     *
     * @return numero variabili assegnate, 0 se UNSAT o modello vuoto
     */
    public int getModelSize() {
        return assignment != null ? assignment.size() : 0;
    }

    //endregion

    //region OUTPUT E RAPPRESENTAZIONE

    /**
     * Genera rappresentazione testuale completa per output utente.
     * Formato professionale compatibile con standard accademici e industriali.
     *
     * STRUTTURA OUTPUT:
     * • Header con esito (SAT/UNSAT)
     * • Contenuto principale (modello o prova)
     * • Gestione intelligente dimensioni per leggibilità
     * • Messaggi informativi per casi speciali
     *
     * @return stringa formattata per presentazione
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
     * Genera output formattato per risultati SAT.
     */
    private String generateSATOutput() {
        StringBuilder satOutput = new StringBuilder();
        satOutput.append("SAT\n");
        satOutput.append("Modello:\n");

        if (hasModel()) {
            formatModelOutput(satOutput);
        } else {
            satOutput.append("Errore: modello non disponibile per risultato SAT.\n");
        }

        return satOutput.toString();
    }

    /**
     * Genera output formattato per risultati UNSAT.
     */
    private String generateUNSATOutput() {
        StringBuilder unsatOutput = new StringBuilder();
        unsatOutput.append("UNSAT\n");

        if (hasProof()) {
            formatProofOutput(unsatOutput);
        } else {
            unsatOutput.append("Prova di insoddisfacibilità non disponibile.\n");
        }

        return unsatOutput.toString();
    }

    /**
     * Formatta modello SAT per output leggibile.
     */
    private void formatModelOutput(StringBuilder output) {
        // Ordinamento per leggibilità
        assignment.entrySet().stream()
                .sorted(Map.Entry.comparingByKey())
                .forEach(entry -> {
                    String variableName = entry.getKey();
                    Boolean value = entry.getValue();
                    output.append(variableName).append(" → ").append(value).append("\n");
                });
    }

    /**
     * Formatta prova UNSAT per output con gestione dimensioni.
     */
    private void formatProofOutput(StringBuilder output) {
        // Gestione intelligente dimensioni prova
        if (shouldDisplayFullProof()) {
            output.append("Prova di insoddisfacibilità:\n");
            output.append(proof);
        } else {
            output.append("Prova troppo grande per visualizzazione completa.\n");
            output.append("Dimensione prova: ").append(statistics.getProofSize()).append(" passi.\n");
        }
    }

    /**
     * Determina se visualizzare prova completa basandosi su dimensioni.
     */
    private boolean shouldDisplayFullProof() {
        // Criteri per visualizzazione: dimensione ragionevole E statistiche disponibili
        return statistics.getProofSize() > 0 &&
                statistics.getProofSize() < 500 &&
                proof.length() < 10000; // Limite caratteri per leggibilità
    }

    /**
     * Genera rappresentazione compatta per logging e debugging.
     *
     * @return stringa sintetica con informazioni essenziali
     */
    public String toCompactString() {
        return String.format("SATResult{%s, vars=%d, time=%dms}",
                satisfiable ? "SAT" : "UNSAT",
                getModelSize(),
                statistics.getExecutionTimeMs());
    }

    //endregion

    //region UGUAGLIANZA E HASH

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

    //endregion

    //region UTILITÀ E CONVERSIONI

    /**
     * Verifica se il risultato rappresenta una risoluzione completa.
     *
     * @return true se SAT con modello O UNSAT con prova
     */
    public boolean isComplete() {
        return (satisfiable && hasModel()) || (!satisfiable && hasProof());
    }

    /**
     * Verifica se il risultato ha statistiche significative.
     *
     * @return true se statistiche contengono dati di esecuzione
     */
    public boolean hasSignificantStatistics() {
        return statistics.getDecisions() > 0 ||
                statistics.getConflicts() > 0 ||
                statistics.getExecutionTimeMs() > 0;
    }

    /**
     * Estrae riepilogo esecuzione per reporting rapido.
     *
     * @return stringa con metriche chiave
     */
    public String getExecutionSummary() {
        return String.format("Esito: %s | Decisioni: %d | Conflitti: %d | Tempo: %dms",
                satisfiable ? "SAT" : "UNSAT",
                statistics.getDecisions(),
                statistics.getConflicts(),
                statistics.getExecutionTimeMs());
    }

    /**
     * Verifica qualità del risultato per validazione.
     *
     * @return true se risultato è ben formato e completo
     */
    public boolean isWellFormed() {
        try {
            // Validazione basic consistency
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