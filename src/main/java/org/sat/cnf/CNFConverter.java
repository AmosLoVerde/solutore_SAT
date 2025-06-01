package org.sat.cnf;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.logging.Logger;
import java.util.logging.Level;

/**
 * Classe che rappresenta una formula durante la conversione in CNF.
 * Consente di tenere traccia del tipo di formula (AND, OR, NOT, ATOM) e dei suoi componenti.
 * Applica le trasformazioni necessarie e semplifica la formula risultante.
 */
public class CNFConverter {

    /** Logger per la registrazione dei messaggi */
    private static final Logger LOGGER = Logger.getLogger(CNFConverter.class.getName());

    public enum Type {
        AND, OR, NOT, ATOM
    }

    public Type type;
    public String atom;                    // usato quando type == ATOM
    public CNFConverter operand;           // usato quando type == NOT
    public List<CNFConverter> operands;    // usato quando type == AND or type == OR

    // Costruttore per atomi
    public CNFConverter(String atom) {
        this.type = Type.ATOM;
        this.atom = atom;
    }

    // Costruttore per operazioni NOT
    public CNFConverter(CNFConverter operand) {
        this.type = Type.NOT;
        this.operand = operand;
    }

    // Costruttore per operazioni AND e OR
    public CNFConverter(Type type, List<CNFConverter> operands) {
        this.type = type;
        this.operands = operands;
    }

    /**
     * Converte la formula in CNF applicando le trasformazioni necessarie.
     * @return formula in CNF
     */
    public CNFConverter toCNF() {
        try {
            CNFConverter result = this;
            //LOGGER.info("Formula originale: " + result);

            // Spinge le negazioni verso gli atomi usando le leggi di De Morgan
            result = result.pushNegations();
            //LOGGER.info("Dopo applicazione negazioni: " + result);

            // Applica la legge distributiva
            result = result.distributeOrOverAnd();
            //LOGGER.info("Dopo distribuzione OR su AND: " + result);

            // Semplifica la formula
            result = result.simplify();
            //LOGGER.info("Formula finale semplificata: " + result);

            return result;
        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Errore durante la conversione CNF", e);
            throw e;
        }
    }

    /**
     * Elimina le implicazioni e le doppie implicazioni dalla formula.
     * @return formula senza implicazioni o biimplicazioni
     */
    private CNFConverter eliminateImplications() {
        // Nota: Le implicazioni dovrebbero già essere eliminate nel parser,
        // ma aggiungiamo un controllo esplicito qui per sicurezza
        return this;
    }

    /**
     * Spinge le negazioni verso gli atomi usando le leggi di De Morgan.
     *
     * !(A v B) diventa (!A ∧ !B)
     * !(A ∧ B) diventa (!A v !B)
     * !!A diventa A
     * @return formula con negazioni applicate agli atomi
     */
    private CNFConverter pushNegations() {
        switch (this.type) {
            case ATOM:
                // Caso base: gli atomi non richiedono trasformazioni
                return this;
            case NOT:
                // Applica la negazione ritornando le trasformazioni
                return applyNegation();
            case OR:
                // Si applica il pushNegations a ogni operando
                // ma si mantiene la struttura dell'OR
                // Esempio: (A v !!B) diventa (A v B)
                List<CNFConverter> orOperands = new ArrayList<>();
                for (CNFConverter op : operands) {
                    orOperands.add(op.pushNegations());
                }
                return new CNFConverter(Type.OR, orOperands);
            case AND:
                // Si applica il pushNegations a ogni operando
                // ma si mantiene la struttura dell'AND
                // Esempio: (A ∧ !!B) diventa (A ∧ B)
                List<CNFConverter> andOperands = new ArrayList<>();
                for (CNFConverter op : operands) {
                    andOperands.add(op.pushNegations());
                }
                return new CNFConverter(Type.AND, andOperands);
            default:
                throw new IllegalStateException("Tipo di formula non supportato");
        }
    }

    /**
     * Applica le leggi di De Morgan per le negazioni.
     * @return formula con negazioni applicate correttamente
     */
    private CNFConverter applyNegation() {
        CNFConverter innerFormula = operand.pushNegations();

        switch (innerFormula.type) {
            case ATOM:
                // !A rimane !A
                return new CNFConverter(innerFormula);
            case NOT:
                // !!A diventa A
                return innerFormula.operand;
            case AND:
                // !(A & B & C) diventa !A | !B | !C
                List<CNFConverter> negatedAnds = new ArrayList<>();
                for (CNFConverter op : innerFormula.operands) {
                    negatedAnds.add(new CNFConverter(op));
                }
                return new CNFConverter(Type.OR, negatedAnds);
            case OR:
                // !(A | B | C) diventa !A & !B & !C
                List<CNFConverter> negatedOrs = new ArrayList<>();
                for (CNFConverter op : innerFormula.operands) {
                    negatedOrs.add(new CNFConverter(op));
                }
                return new CNFConverter(Type.AND, negatedOrs);
            default:
                throw new IllegalStateException("Tipo di formula non supportato");
        }
    }

    /**
     * Distribuisce OR sopra AND usando la proprietà distributiva.
     * @return formula con OR distribuito su AND
     */
    private CNFConverter distributeOrOverAnd() {
        // Prima converte ricorsivamente tutti gli operandi
        switch (this.type) {
            case ATOM:
                return this;
            case NOT:
                // Verifica che la negazione contenga solo atomi
                if (operand.type == Type.ATOM) {
                    return this;
                } else {
                    // Applica pushNegations nuovamente per assicurarsi che le negazioni
                    // siano state spinte correttamente
                    CNFConverter pushed = this.pushNegations();
                    // Se il risultato è ancora una negazione non di un atomo, c'è un problema
                    if (pushed.type == Type.NOT && pushed.operand.type != Type.ATOM) {
                        //LOGGER.severe("Negazione non risolta: " + this);
                        throw new IllegalStateException("Le negazioni dovrebbero essere già state spinte verso gli atomi");
                    }
                    return pushed;
                }
            case AND:
                // Distribuisce ricorsivamente su tutti gli operandi AND
                List<CNFConverter> andOperands = new ArrayList<>();
                for (CNFConverter op : operands) {
                    andOperands.add(op.distributeOrOverAnd());
                }
                return new CNFConverter(Type.AND, andOperands);
            case OR:
                return distributeOrHelper();
            default:
                throw new IllegalStateException("Tipo di formula non supportato");
        }
    }

    /**
     * Helper per distribuire OR sopra AND.
     * @return formula con OR distribuito su AND
     */
    private CNFConverter distributeOrHelper() {
        // Prima converte ricorsivamente tutti gli operandi OR
        List<CNFConverter> processedOrs = new ArrayList<>();
        for (CNFConverter op : operands) {
            // Assicuriamoci che qualsiasi negazione sia gestita correttamente
            CNFConverter processed = op;
            // Se l'operando è una negazione che contiene una struttura complessa,
            // applichiamo pushNegations prima
            if (processed.type == Type.NOT && processed.operand.type != Type.ATOM) {
                processed = processed.pushNegations();
            }
            processedOrs.add(processed.distributeOrOverAnd());
        }

        // Cerca un operando AND su cui distribuire
        CNFConverter andOperand = null;
        int andIndex = -1;

        for (int i = 0; i < processedOrs.size(); i++) {
            if (processedOrs.get(i).type == Type.AND) {
                andOperand = processedOrs.get(i);
                andIndex = i;
                break;
            }
        }

        // Se non troviamo AND, la formula è già in forma distributiva
        if (andOperand == null) {
            return new CNFConverter(Type.OR, processedOrs);
        }

        // Rimuove l'operando AND dall'elenco
        processedOrs.remove(andIndex);

        // Crea la lista dei termini da distribuire (tutto tranne l'AND)
        List<CNFConverter> otherTerms = processedOrs;

        // Ora distribuisce: (A | B | (C & D)) diventa (A | B | C) & (A | B | D)
        List<CNFConverter> resultClauses = new ArrayList<>();
        for (CNFConverter andTerm : andOperand.operands) {
            List<CNFConverter> newOrTerms = new ArrayList<>(otherTerms);
            newOrTerms.add(andTerm);
            CNFConverter newOr = new CNFConverter(Type.OR, newOrTerms);
            // Distribuisce ricorsivamente in caso di AND nidificati
            resultClauses.add(newOr.distributeOrOverAnd());
        }

        return new CNFConverter(Type.AND, resultClauses);
    }

    /**
     * Semplifica la formula eliminando ridondanze.
     * @return formula semplificata
     */
    private CNFConverter simplify() {
        switch (this.type) {
            case ATOM:
                return this;
            case NOT:
                // Verifica che la negazione contenga solo atomi
                if (operand.type == Type.ATOM) {
                    return this;
                } else {
                    // Applica pushNegations nuovamente
                    CNFConverter pushed = this.pushNegations();
                    return pushed.simplify();
                }
            case AND:
                // Appiattisce AND nidificati e rimuove duplicati
                List<CNFConverter> flattenedAnds = new ArrayList<>();
                for (CNFConverter op : operands) {
                    CNFConverter simplified = op.simplify();
                    if (simplified.type == Type.AND) {
                        for (CNFConverter nested : simplified.operands) {
                            addUniqueClause(flattenedAnds, nested);
                        }
                    } else {
                        addUniqueClause(flattenedAnds, simplified);
                    }
                }
                if (flattenedAnds.size() == 1) {
                    return flattenedAnds.get(0);
                }
                return new CNFConverter(Type.AND, flattenedAnds);
            case OR:
                // Appiattisce OR nidificati e rimuove duplicati
                List<CNFConverter> flattenedOrs = new ArrayList<>();
                Set<String> atomsInClause = new HashSet<>();
                boolean hasContradiction = false;

                for (CNFConverter op : operands) {
                    CNFConverter simplified = op.simplify();
                    if (simplified.type == Type.OR) {
                        for (CNFConverter nested : simplified.operands) {
                            // Rimosso il controllo che inseriva TRUE in caso di contraddizione
                            addToClauseWithoutCheck(flattenedOrs, nested);
                        }
                    } else {
                        // Rimosso il controllo che inseriva TRUE in caso di contraddizione
                        addToClauseWithoutCheck(flattenedOrs, simplified);
                    }
                }

                // Rimosso il controllo che restituiva TRUE in caso di contraddizione

                if (flattenedOrs.size() == 1) {
                    return flattenedOrs.get(0);
                }
                return new CNFConverter(Type.OR, flattenedOrs);
            default:
                throw new IllegalStateException("Tipo di formula non supportato");
        }
    }

    /**
     * Aggiunge una clausola unica alla lista di clausole.
     * @param clauses lista di clausole
     * @param clause clausola da aggiungere
     */
    private void addUniqueClause(List<CNFConverter> clauses, CNFConverter clause) {
        if (!clauses.contains(clause)) {
            clauses.add(clause);
        }
    }

    /**
     * Aggiunge un letterale alla clausola senza controllare contraddizioni.
     * @param clauseTerms termini della clausola
     * @param term termine da aggiungere
     */
    private void addToClauseWithoutCheck(List<CNFConverter> clauseTerms, CNFConverter term) {
        // Semplicemente aggiunge il termine senza controllare contraddizioni
        addUniqueClause(clauseTerms, term);
    }

    /**
     * Verifica se due formule sono uguali.
     * @param obj oggetto da confrontare
     * @return true se le formule sono uguali
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;

        CNFConverter that = (CNFConverter) obj;
        if (this.type != that.type) return false;

        switch (this.type) {
            case ATOM:
                return this.atom.equals(that.atom);
            case NOT:
                return this.operand.equals(that.operand);
            case AND:
            case OR:
                if (this.operands.size() != that.operands.size()) return false;
                return new HashSet<>(this.operands).equals(new HashSet<>(that.operands));
            default:
                return false;
        }
    }

    /**
     * Calcola l'hashcode della formula.
     * @return hashcode
     */
    @Override
    public int hashCode() {
        int result = type.hashCode();
        switch (type) {
            case ATOM:
                result = 31 * result + atom.hashCode();
                break;
            case NOT:
                result = 31 * result + operand.hashCode();
                break;
            case AND:
            case OR:
                for (CNFConverter op : operands) {
                    result = 31 * result + op.hashCode();
                }
                break;
        }
        return result;
    }

    /**
     * Converte la formula in una rappresentazione stringa.
     * @return rappresentazione stringa della formula
     */
    @Override
    public String toString() {
        switch (this.type) {
            case ATOM:
                return atom;
            case NOT:
                if (operand.type == Type.ATOM) {
                    return "!" + operand;
                } else {
                    return "!(" + operand + ")";
                }
            case AND:
                if (operands.isEmpty()) return "";
                if (operands.size() == 1) return operands.get(0).toString();

                StringBuilder andResult = new StringBuilder();
                for (int i = 0; i < operands.size(); i++) {
                    if (i > 0) {
                        andResult.append(" & ");
                    }

                    CNFConverter op = operands.get(i);
                    if (op.type == Type.OR) {
                        andResult.append("(").append(op).append(")");
                    } else {
                        andResult.append(op);
                    }
                }
                return andResult.toString();

            case OR:
                if (operands.isEmpty()) return "";
                if (operands.size() == 1) return operands.get(0).toString();

                StringBuilder orResult = new StringBuilder();
                for (int i = 0; i < operands.size(); i++) {
                    if (i > 0) {
                        orResult.append(" | ");
                    }
                    orResult.append(operands.get(i));
                }
                return orResult.toString();

            default:
                throw new IllegalStateException("Tipo di formula non supportato");
        }
    }
}