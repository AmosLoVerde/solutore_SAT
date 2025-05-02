package org.sat.cnf;

import org.sat.antlr.org.sat.parser.LogicFormulaBaseVisitor;
import org.sat.antlr.org.sat.parser.LogicFormulaParser;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.logging.Logger;
import java.util.logging.Level;

/**
 * Convertitore migliorato per trasformare formule logiche in forma normale congiuntiva (CNF).
 * Implementa un visitor per l'albero di parsing generato dalla grammatica LogicFormula.
 * Applica le trasformazioni necessarie e semplifica la formula risultante.
 *
 * @author Amos Lo Verde
 * @version 1.2.1
 */
public class CNFConverter extends LogicFormulaBaseVisitor<CNFConverter.Formula> {

    /** Logger per la registrazione dei messaggi */
    private static final Logger LOGGER = Logger.getLogger(CNFConverter.class.getName());

    /**
     * Classe interna che rappresenta una formula durante la conversione.
     * Consente di tenere traccia del tipo di formula (AND, OR, NOT, ATOM) e dei suoi componenti.
     */
    protected static class Formula {
        enum Type {
            AND, OR, NOT, ATOM
        }

        Type type;
        String atom;                // usato quando type == ATOM
        Formula operand;            // usato quando type == NOT
        List<Formula> operands;     // usato quando type == AND or type == OR

        // Costruttore per atomi
        Formula(String atom) {
            this.type = Type.ATOM;
            this.atom = atom;
        }

        // Costruttore per operazioni NOT
        Formula(Formula operand) {
            this.type = Type.NOT;
            this.operand = operand;
        }

        // Costruttore per operazioni AND e OR
        Formula(Type type, List<Formula> operands) {
            this.type = type;
            this.operands = operands;
        }

        /**
         * Converte la formula in CNF applicando le trasformazioni necessarie.
         * @return formula in CNF
         */
        public Formula toCNF() {
            try {
                Formula result = this;
                //LOGGER.info("Formula originale: " + result);

                // Elimina le implicazioni e le doppie implicazioni
                result = result.eliminateImplications();
                //LOGGER.info("Dopo eliminazione implicazioni: " + result);

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
        private Formula eliminateImplications() {
            // Nota: Le implicazioni dovrebbero già essere eliminate nel parser,
            // ma aggiungiamo un controllo esplicito qui per sicurezza
            return this;
        }

        /**
         * Spinge le negazioni verso gli atomi usando le leggi di De Morgan.
         * @return formula con negazioni applicate agli atomi
         */
        private Formula pushNegations() {
            switch (this.type) {
                case ATOM:
                    return this;
                case NOT:
                    return applyNegation();
                case OR:
                    List<Formula> orOperands = new ArrayList<>();
                    for (Formula op : operands) {
                        orOperands.add(op.pushNegations());
                    }
                    return new Formula(Type.OR, orOperands);
                case AND:
                    List<Formula> andOperands = new ArrayList<>();
                    for (Formula op : operands) {
                        andOperands.add(op.pushNegations());
                    }
                    return new Formula(Type.AND, andOperands);
                default:
                    throw new IllegalStateException("Tipo di formula non supportato");
            }
        }

        /**
         * Applica le leggi di De Morgan per le negazioni.
         * @return formula con negazioni applicate correttamente
         */
        private Formula applyNegation() {
            Formula innerFormula = operand.pushNegations();

            switch (innerFormula.type) {
                case ATOM:
                    // !A rimane !A
                    return new Formula(innerFormula);
                case NOT:
                    // !!A diventa A
                    return innerFormula.operand;
                case AND:
                    // !(A & B & C) diventa !A | !B | !C
                    List<Formula> negatedAnds = new ArrayList<>();
                    for (Formula op : innerFormula.operands) {
                        negatedAnds.add(new Formula(op));
                    }
                    return new Formula(Type.OR, negatedAnds);
                case OR:
                    // !(A | B | C) diventa !A & !B & !C
                    List<Formula> negatedOrs = new ArrayList<>();
                    for (Formula op : innerFormula.operands) {
                        negatedOrs.add(new Formula(op));
                    }
                    return new Formula(Type.AND, negatedOrs);
                default:
                    throw new IllegalStateException("Tipo di formula non supportato");
            }
        }

        /**
         * Distribuisce OR sopra AND usando la proprietà distributiva.
         * @return formula con OR distribuito su AND
         */
        private Formula distributeOrOverAnd() {
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
                        Formula pushed = this.pushNegations();
                        // Se il risultato è ancora una negazione non di un atomo, c'è un problema
                        if (pushed.type == Type.NOT && pushed.operand.type != Type.ATOM) {
                            //LOGGER.severe("Negazione non risolta: " + this);
                            throw new IllegalStateException("Le negazioni dovrebbero essere già state spinte verso gli atomi");
                        }
                        return pushed;
                    }
                case AND:
                    // Distribuisce ricorsivamente su tutti gli operandi AND
                    List<Formula> andOperands = new ArrayList<>();
                    for (Formula op : operands) {
                        andOperands.add(op.distributeOrOverAnd());
                    }
                    return new Formula(Type.AND, andOperands);
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
        private Formula distributeOrHelper() {
            // Prima converte ricorsivamente tutti gli operandi OR
            List<Formula> processedOrs = new ArrayList<>();
            for (Formula op : operands) {
                // Assicuriamoci che qualsiasi negazione sia gestita correttamente
                Formula processed = op;
                // Se l'operando è una negazione che contiene una struttura complessa,
                // applichiamo pushNegations prima
                if (processed.type == Type.NOT && processed.operand.type != Type.ATOM) {
                    processed = processed.pushNegations();
                }
                processedOrs.add(processed.distributeOrOverAnd());
            }

            // Cerca un operando AND su cui distribuire
            Formula andOperand = null;
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
                return new Formula(Type.OR, processedOrs);
            }

            // Rimuove l'operando AND dall'elenco
            processedOrs.remove(andIndex);

            // Crea la lista dei termini da distribuire (tutto tranne l'AND)
            List<Formula> otherTerms = processedOrs;

            // Ora distribuisce: (A | B | (C & D)) diventa (A | B | C) & (A | B | D)
            List<Formula> resultClauses = new ArrayList<>();
            for (Formula andTerm : andOperand.operands) {
                List<Formula> newOrTerms = new ArrayList<>(otherTerms);
                newOrTerms.add(andTerm);
                Formula newOr = new Formula(Type.OR, newOrTerms);
                // Distribuisce ricorsivamente in caso di AND nidificati
                resultClauses.add(newOr.distributeOrOverAnd());
            }

            return new Formula(Type.AND, resultClauses);
        }

        /**
         * Semplifica la formula eliminando ridondanze.
         * @return formula semplificata
         */
        private Formula simplify() {
            switch (this.type) {
                case ATOM:
                    return this;
                case NOT:
                    // Verifica che la negazione contenga solo atomi
                    if (operand.type == Type.ATOM) {
                        return this;
                    } else {
                        // Applica pushNegations nuovamente
                        Formula pushed = this.pushNegations();
                        return pushed.simplify();
                    }
                case AND:
                    // Appiattisce AND nidificati e rimuove duplicati
                    List<Formula> flattenedAnds = new ArrayList<>();
                    for (Formula op : operands) {
                        Formula simplified = op.simplify();
                        if (simplified.type == Type.AND) {
                            for (Formula nested : simplified.operands) {
                                addUniqueClause(flattenedAnds, nested);
                            }
                        } else {
                            addUniqueClause(flattenedAnds, simplified);
                        }
                    }
                    if (flattenedAnds.size() == 1) {
                        return flattenedAnds.get(0);
                    }
                    return new Formula(Type.AND, flattenedAnds);
                case OR:
                    // Appiattisce OR nidificati e rimuove duplicati
                    List<Formula> flattenedOrs = new ArrayList<>();
                    Set<String> atomsInClause = new HashSet<>();
                    boolean hasContradiction = false;

                    for (Formula op : operands) {
                        Formula simplified = op.simplify();
                        if (simplified.type == Type.OR) {
                            for (Formula nested : simplified.operands) {
                                // Rimosso il controllo che inseriva TRUE in caso di contraddizione
                                addToClauseWithoutCheck(flattenedOrs, nested);
                            }
                        } else {
                            // Rimosso il controllo che inseriva TRUE in caso di contraddizione
                            addToClauseWithoutCheck(flattenedOrs, simplified);
                        }
                    }

                    // Rimosso il controllo che restituiva TRUE in caso di contraddizione
                    /* RIMOSSO:
                    // Se la clausola contiene sia un letterale che la sua negazione, è sempre vera (tautologia)
                    if (hasContradiction) {
                        return new Formula("TRUE");
                    }
                    */

                    if (flattenedOrs.size() == 1) {
                        return flattenedOrs.get(0);
                    }
                    return new Formula(Type.OR, flattenedOrs);
                default:
                    throw new IllegalStateException("Tipo di formula non supportato");
            }
        }

        /**
         * Aggiunge una clausola unica alla lista di clausole.
         * @param clauses lista di clausole
         * @param clause clausola da aggiungere
         */
        private void addUniqueClause(List<Formula> clauses, Formula clause) {
            if (!clauses.contains(clause)) {
                clauses.add(clause);
            }
        }

        /**
         * Aggiunge un letterale alla clausola senza controllare contraddizioni.
         * @param clauseTerms termini della clausola
         * @param term termine da aggiungere
         */
        private void addToClauseWithoutCheck(List<Formula> clauseTerms, Formula term) {
            // Semplicemente aggiunge il termine senza controllare contraddizioni
            addUniqueClause(clauseTerms, term);
        }

        /* RIMOSSO/COMMENTATO:
        private boolean addToClauseWithCheck(List<Formula> clauseTerms, Formula term, Set<String> atomsInClause) {
            if (term.type == Type.ATOM) {
                String atom = term.atom;
                // Controlla se la negazione dell'atomo è già presente
                if (atomsInClause.contains("!" + atom)) {
                    return true;  // Contraddizione trovata
                }
                atomsInClause.add(atom);
                addUniqueClause(clauseTerms, term);
            } else if (term.type == Type.NOT && term.operand.type == Type.ATOM) {
                String atom = term.operand.atom;
                // Controlla se l'atomo è già presente
                if (atomsInClause.contains(atom)) {
                    return true;  // Contraddizione trovata
                }
                atomsInClause.add("!" + atom);
                addUniqueClause(clauseTerms, term);
            } else {
                addUniqueClause(clauseTerms, term);
            }
            return false;
        }
        */

        /**
         * Verifica se due formule sono uguali.
         * @param obj oggetto da confrontare
         * @return true se le formule sono uguali
         */
        @Override
        public boolean equals(Object obj) {
            if (this == obj) return true;
            if (obj == null || getClass() != obj.getClass()) return false;

            Formula that = (Formula) obj;
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
                    for (Formula op : operands) {
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

                        Formula op = operands.get(i);
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

    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    // ~~~~~~~~~~~~~~~~~~~~~~~~~< VISITORS >~~~~~~~~~~~~~~~~~~~~~~~~~
    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    /**
     * Punto di ingresso per la conversione di una formula in CNF.
     * Visita l'intera formula e restituisce la rappresentazione CNF.
     *
     * @param ctx contesto della formula completa
     * @return formula in CNF
     */
    @Override
    public Formula visitFormula(LogicFormulaParser.FormulaContext ctx) {
        Formula formula = visit(ctx.biconditional());
        return formula.toCNF();
    }

    /**
     * Gestisce la conversione della doppia implicazione (IFF) in CNF.
     * A <-> B diventa (A -> B) & (B -> A)
     *
     * @param ctx contesto della doppia implicazione
     * @return formula oggetto
     */
    @Override
    public Formula visitIff(LogicFormulaParser.IffContext ctx) {
        // Se non ci sono operatori IFF, si procede con l'implicazione
        if (ctx.IFF().isEmpty()) {
            return visit(ctx.implication(0));
        }

        // Per gestire catene di doppie implicazioni: A <-> B <-> C
        List<Formula> andOperands = new ArrayList<>();

        for (int i = 0; i < ctx.implication().size() - 1; i++) {
            Formula left = visit(ctx.implication(i));
            Formula right = visit(ctx.implication(i + 1));

            // A <-> B equivale a (A -> B) & (B -> A)
            // ovvero (!A | B) & (!B | A)

            // (!A | B)
            List<Formula> leftToRightOr = new ArrayList<>();
            leftToRightOr.add(new Formula(left));   // !A
            leftToRightOr.add(right);               // B
            Formula leftToRight = new Formula(Formula.Type.OR, leftToRightOr);

            // (!B | A)
            List<Formula> rightToLeftOr = new ArrayList<>();
            rightToLeftOr.add(new Formula(right));  // !B
            rightToLeftOr.add(left);                // A
            Formula rightToLeft = new Formula(Formula.Type.OR, rightToLeftOr);

            andOperands.add(leftToRight);
            andOperands.add(rightToLeft);
        }

        return new Formula(Formula.Type.AND, andOperands);
    }

    /**
     * Gestisce la conversione dell'implicazione (IMPLIES) in CNF.
     * A -> B diventa !A | B
     *
     * @param ctx contesto dell'implicazione
     * @return formula oggetto
     */
    @Override
    public Formula visitImplies(LogicFormulaParser.ImpliesContext ctx) {
        // Se non c'è l'operatore IMPLIES, procede con la disgiunzione
        if (ctx.IMPLIES() == null) {
            return visit(ctx.disjunction());
        }

        // A -> B equivale a !A | B
        Formula left = visit(ctx.disjunction());
        Formula right = visit(ctx.implication());

        // Crea !A | B
        List<Formula> orOperands = new ArrayList<>();
        orOperands.add(new Formula(left));   // !A
        orOperands.add(right);               // B

        return new Formula(Formula.Type.OR, orOperands);
    }

    /**
     * Gestisce la conversione della disgiunzione (OR).
     *
     * @param ctx contesto della disgiunzione
     * @return formula oggetto
     */
    @Override
    public Formula visitOr(LogicFormulaParser.OrContext ctx) {
        // Se c'è solo una congiunzione, la visita direttamente
        if (ctx.conjunction().size() == 1) {
            return visit(ctx.conjunction(0));
        }

        List<Formula> orOperands = new ArrayList<>();

        // Raccoglie tutti gli operandi OR
        for (LogicFormulaParser.ConjunctionContext conjCtx : ctx.conjunction()) {
            orOperands.add(visit(conjCtx));
        }

        return new Formula(Formula.Type.OR, orOperands);
    }

    /**
     * Gestisce la conversione della congiunzione (AND).
     *
     * @param ctx contesto della congiunzione
     * @return formula oggetto
     */
    @Override
    public Formula visitAnd(LogicFormulaParser.AndContext ctx) {
        // Se c'è solo una negazione, la visita direttamente
        if (ctx.negation().size() == 1) {
            return visit(ctx.negation(0));
        }

        List<Formula> andOperands = new ArrayList<>();

        // Raccoglie tutti gli operandi AND
        for (LogicFormulaParser.NegationContext negCtx : ctx.negation()) {
            andOperands.add(visit(negCtx));
        }

        return new Formula(Formula.Type.AND, andOperands);
    }

    /**
     * Gestisce la conversione della negazione (NOT).
     *
     * @param ctx contesto della negazione
     * @return formula oggetto
     */
    @Override
    public Formula visitNot(LogicFormulaParser.NotContext ctx) {
        Formula innerFormula = visit(ctx.negation());
        return new Formula(innerFormula);
    }

    /**
     * Gestisce la visita di una variabile.
     *
     * @param ctx contesto della variabile
     * @return formula oggetto
     */
    @Override
    public Formula visitVar(LogicFormulaParser.VarContext ctx) {
        return visit(ctx.atom());
    }

    /**
     * Gestisce la visita di espressioni in parentesi.
     *
     * @param ctx contesto delle parentesi
     * @return formula oggetto
     */
    @Override
    public Formula visitPar(LogicFormulaParser.ParContext ctx) {
        return visit(ctx.biconditional());
    }

    /**
     * Gestisce la visita di un identificatore.
     *
     * @param ctx contesto dell'identificatore
     * @return formula oggetto
     */
    @Override
    public Formula visitId(LogicFormulaParser.IdContext ctx) {
        return new Formula(ctx.IDENTIFIER().getText());
    }

    /**
     * Gestisce la visita della costante TRUE.
     *
     * @param ctx contesto della costante TRUE
     * @return formula oggetto
     */
    @Override
    public Formula visitTrue(LogicFormulaParser.TrueContext ctx) {
        return new Formula("TRUE");
    }

    /**
     * Gestisce la visita della costante FALSE.
     *
     * @param ctx contesto della costante FALSE
     * @return formula oggetto
     */
    @Override
    public Formula visitFalse(LogicFormulaParser.FalseContext ctx) {
        return new Formula("FALSE");
    }
}