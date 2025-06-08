package org.sat.support;

import java.util.*;

/**
 * LETTERALE ASSEGNATO - Modello completo di variabile assegnata con metadata genealogici
 *
 * Rappresenta una variabile assegnata durante l'algoritmo CDCL con tutti i metadata necessari
 * per tracking completo, backtracking efficiente e analisi dei conflitti. Incapsula tutte
 * le informazioni genealogiche dell'assegnamento per supportare operazioni avanzate.
 *
 * INFORMAZIONI MEMORIZZATE:
 * • Identificazione variabile e valore assegnato
 * • Tipo assegnamento (decisione euristica vs implicazione)
 * • Clausola ancestrale per implicazioni (genealogia)
 * • Validazioni comprehensive per consistenza dati
 * • Interfaccia immutabile per thread-safety
 *
 * UTILIZZI NELL'ALGORITMO CDCL:
 * • Tracking cronologia decisioni per backtracking
 * • Identificazione catene di implicazioni per conflict analysis
 * • Generazione spiegazioni matematiche per prove
 * • Ricostruzione modelli SAT con tracciabilità
 */
public class AssignedLiteral {

    //region ATTRIBUTI CORE DELL'ASSEGNAMENTO

    /**
     * ID numerico della variabile assegnata.
     * Corrisponde agli ID generati da CNFFormula (sempre > 0).
     * Invariante: valore immutabile e sempre positivo.
     */
    private final Integer variable;

    /**
     * Valore booleano assegnato alla variabile.
     * • true: variabile impostata a vero
     * • false: variabile impostata a falso
     * Invariante: non null, valore immutabile.
     */
    private final Boolean value;

    /**
     * Tipo di assegnamento per distinguere origini diverse.
     * • true: decisione euristica presa dal decision maker
     * • false: implicazione derivata da unit propagation
     * Invariante: non null, determina comportamento backtracking.
     */
    private final Boolean isDecision;

    /**
     * Clausola che ha causato questa implicazione (genealogia).
     * • null per decisioni euristiche (auto-giustificate)
     * • Lista non vuota per implicazioni (clausola unit causante)
     * Invariante: consistenza con tipo assegnamento.
     */
    private final List<Integer> ancestorClause;

    //endregion

    //region COSTRUZIONE CON VALIDAZIONE COMPLETA

    /**
     * Costruisce letterale assegnato con validazione completa di tutti i parametri.
     *
     * VALIDAZIONI APPLICATE:
     * • Variable ID deve essere > 0 (range valido per formula)
     * • Value non può essere null (assegnamento completo richiesto)
     * • IsDecision non può essere null (tipo deve essere definito)
     * • Implicazioni richiedono clausola ancestrale non vuota
     * • Decisioni non dovrebbero avere clausola ancestrale
     * • Clausola ancestrale deve contenere solo letterali validi
     *
     * @param variable ID numerico variabile (> 0)
     * @param value valore booleano assegnato (non null)
     * @param isDecision true se decisione, false se implicazione
     * @param ancestorClause clausola causante (richiesta per implicazioni)
     * @throws IllegalArgumentException se parametri inconsistenti o malformati
     */
    public AssignedLiteral(Integer variable, Boolean value, Boolean isDecision, List<Integer> ancestorClause) {
        // Validazione parametri di base
        validateBasicParameters(variable, value, isDecision);

        // Validazione coerenza tipo-clausola
        validateTypeClauseConsistency(isDecision, ancestorClause);

        // Validazione contenuto clausola ancestrale
        if (ancestorClause != null) {
            validateAncestorClauseContent(ancestorClause);
        }

        // Assegnazione con copia difensiva
        this.variable = variable;
        this.value = value;
        this.isDecision = isDecision;
        this.ancestorClause = ancestorClause != null ?
                Collections.unmodifiableList(new ArrayList<>(ancestorClause)) : null;
    }

    /**
     * Valida parametri di base per consistenza e range.
     */
    private void validateBasicParameters(Integer variable, Boolean value, Boolean isDecision) {
        if (variable == null || variable <= 0) {
            throw new IllegalArgumentException("Variable ID deve essere > 0, ricevuto: " + variable);
        }
        if (value == null) {
            throw new IllegalArgumentException("Value non può essere null");
        }
        if (isDecision == null) {
            throw new IllegalArgumentException("IsDecision non può essere null");
        }
    }

    /**
     * Valida coerenza tra tipo assegnamento e presenza clausola ancestrale.
     */
    private void validateTypeClauseConsistency(Boolean isDecision, List<Integer> ancestorClause) {
        if (!isDecision && (ancestorClause == null || ancestorClause.isEmpty())) {
            throw new IllegalArgumentException("Implicazioni richiedono clausola ancestrale non vuota");
        }
        if (isDecision && ancestorClause != null && !ancestorClause.isEmpty()) {
            throw new IllegalArgumentException("Decisioni non dovrebbero avere clausola ancestrale");
        }
    }

    /**
     * Valida contenuto clausola ancestrale per consistenza.
     */
    private void validateAncestorClauseContent(List<Integer> ancestorClause) {
        for (Integer literal : ancestorClause) {
            if (literal == null || literal == 0) {
                throw new IllegalArgumentException("Clausola ancestrale contiene letterale non valido: " + literal);
            }
        }
    }

    //endregion

    //region INTERFACCIA PUBBLICA ACCESSORS

    /**
     * @return ID numerico della variabile assegnata
     */
    public Integer getVariable() {
        return variable;
    }

    /**
     * @return valore booleano assegnato alla variabile
     */
    public Boolean getValue() {
        return value;
    }

    /**
     * @return true se assegnamento è decisione euristica
     */
    public Boolean isDecision() {
        return isDecision;
    }

    /**
     * @return true se assegnamento è implicazione da unit propagation
     */
    public Boolean isImplication() {
        return !isDecision;
    }

    /**
     * @return copia immutabile clausola ancestrale (null per decisioni)
     */
    public List<Integer> getAncestorClause() {
        return ancestorClause; // Già immutabile per costruzione
    }

    /**
     * @return true se esiste clausola ancestrale valida
     */
    public boolean hasAncestorClause() {
        return ancestorClause != null && !ancestorClause.isEmpty();
    }

    //endregion

    //region UTILITÀ E CONVERSIONI

    /**
     * Converte assegnamento in letterale DIMACS standard.
     * @return ID positivo se variabile true, negativo se false
     */
    public Integer toDIMACSLiteral() {
        return value ? variable : -variable;
    }

    /**
     * Genera descrizione testuale completa per debugging e logging.
     */
    @Override
    public String toString() {
        StringBuilder description = new StringBuilder();
        description.append("AssignedLiteral{");
        description.append("var=").append(variable);
        description.append(", val=").append(value);
        description.append(", type=").append(isDecision ? "DECISION" : "IMPLICATION");

        if (hasAncestorClause()) {
            description.append(", ancestor=").append(ancestorClause);
        }

        description.append('}');
        return description.toString();
    }

    /**
     * Uguaglianza basata su variabile, valore e tipo (ignora clausola ancestrale).
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;

        AssignedLiteral other = (AssignedLiteral) obj;
        return Objects.equals(variable, other.variable) &&
                Objects.equals(value, other.value) &&
                Objects.equals(isDecision, other.isDecision);
    }

    /**
     * Hash code consistente con equals per uso in collezioni.
     */
    @Override
    public int hashCode() {
        return Objects.hash(variable, value, isDecision);
    }

    //endregion
}