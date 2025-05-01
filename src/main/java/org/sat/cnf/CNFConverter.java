package org.sat.cnf;

import org.sat.antlr.org.sat.parser.LogicFormulaBaseVisitor;
import org.sat.antlr.org.sat.parser.LogicFormulaParser;

import java.util.ArrayList;
import java.util.List;

/**
 * Convertitore per trasformare formule logiche in forma normale congiuntiva (CNF).
 * Implementa un visitor per l'albero di parsing generato dalla grammatica LogicFormula.
 * Applica le trasformazioni necessarie e semplifica la formula risultante.
 *
 * @author Amos Lo Verde
 * @version 1.0.0
 */
public class CNFConverter extends LogicFormulaBaseVisitor<CNFConverter.Formula> {

    /**
     * Classe interna che rappresenta una formula durante la conversione.
     * Consente di tenere traccia del tipo di formula (AND, OR, NOT, ATOM) e dei suoi componenti.
     */
    protected static class Formula {
        enum Type {
            AND, OR, NOT, ATOM
        }

        Type type;
        String atom;  // usato quando type == ATOM
        Formula operand;  // usato quando type == NOT
        List<Formula> operands;  // usato quando type == AND or type == OR

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
            switch (this.type) {
                case ATOM:
                    return this;
                case NOT:
                    return applyNegation();
                case OR:
                    return distributeOr();
                case AND:
                    return flattenAnd();
                default:
                    throw new IllegalStateException("Tipo di formula non supportato");
            }
        }

        /**
         * Applica le leggi di De Morgan per le negazioni.
         * @return formula con negazioni applicate correttamente
         */
        private Formula applyNegation() {
            Formula innerFormula = operand.toCNF();

            switch (innerFormula.type) {
                case ATOM:
                    // !A rimane !A
                    Formula notAtom = new Formula(Type.NOT, new ArrayList<>());
                    notAtom.operand = innerFormula;
                    return notAtom;
                case NOT:
                    // !!A diventa A
                    return innerFormula.operand;
                case AND:
                    // !(A & B & C) diventa !A | !B | !C
                    List<Formula> negatedOperands = new ArrayList<>();
                    for (Formula op : innerFormula.operands) {
                        Formula negated = new Formula(op);
                        negatedOperands.add(negated.toCNF());
                    }
                    return new Formula(Type.OR, negatedOperands).toCNF();
                case OR:
                    // !(A | B | C) diventa !A & !B & !C
                    List<Formula> negatedOrs = new ArrayList<>();
                    for (Formula op : innerFormula.operands) {
                        Formula negated = new Formula(op);
                        negatedOrs.add(negated.toCNF());
                    }
                    return new Formula(Type.AND, negatedOrs).toCNF();
                default:
                    throw new IllegalStateException("Tipo di formula non supportato");
            }
        }

        /**
         * Applica la legge distributiva per OR sopra AND.
         * (A | (B & C) diventa (A | B) & (A | C)
         * @return formula con OR distribuito correttamente
         */
        private Formula distributeOr() {
            // Prima converte tutti gli operandi in CNF
            List<Formula> cnfOperands = new ArrayList<>();
            for (Formula op : operands) {
                cnfOperands.add(op.toCNF());
            }

            // Cerca un operando AND su cui distribuire
            int andIndex = -1;
            for (int i = 0; i < cnfOperands.size(); i++) {
                if (cnfOperands.get(i).type == Type.AND) {
                    andIndex = i;
                    break;
                }
            }

            // Se non c'è nessun AND, mantiene una semplice disgiunzione
            if (andIndex == -1) {
                // Appiattisce gli operatori OR nidificati
                List<Formula> flattenedOrs = new ArrayList<>();
                for (Formula op : cnfOperands) {
                    if (op.type == Type.OR) {
                        flattenedOrs.addAll(op.operands);
                    } else {
                        flattenedOrs.add(op);
                    }
                }
                return new Formula(Type.OR, flattenedOrs);
            }

            // Applica la distribuzione: (A | B | (C & D)) => (A | B | C) & (A | B | D)
            Formula andFormula = cnfOperands.get(andIndex);
            cnfOperands.remove(andIndex);

            List<Formula> distributedClauses = new ArrayList<>();
            for (Formula andOperand : andFormula.operands) {
                List<Formula> newOrOperands = new ArrayList<>(cnfOperands);
                if (andOperand.type == Type.AND) {
                    // Distribuisce su AND nidificati
                    for (Formula nestedAnd : andOperand.operands) {
                        newOrOperands.add(nestedAnd);
                    }
                } else {
                    newOrOperands.add(andOperand);
                }
                Formula newOr = new Formula(Type.OR, newOrOperands);
                distributedClauses.add(newOr.toCNF());  // Ricorsivamente distribuisce
            }

            return new Formula(Type.AND, distributedClauses).toCNF();
        }

        /**
         * Appiattisce le congiunzioni nidificate.
         * @return formula con AND appiattiti
         */
        private Formula flattenAnd() {
            List<Formula> flattenedOperands = new ArrayList<>();

            for (Formula op : operands) {
                Formula cnfOp = op.toCNF();
                if (cnfOp.type == Type.AND) {
                    // Appiattisce AND nidificati
                    flattenedOperands.addAll(cnfOp.operands);
                } else {
                    flattenedOperands.add(cnfOp);
                }
            }

            return new Formula(Type.AND, flattenedOperands);
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
     * Gestisce la conversione della biimplicazione (IFF) in CNF.
     * A <-> B diventa (A -> B) & (B -> A)
     *
     * @param ctx contesto della biimplicazione
     * @return formula oggetto
     */
    @Override
    public Formula visitIff(LogicFormulaParser.IffContext ctx) {
        // Se non ci sono operatori IFF, si procede con l'implicazione
        if (ctx.IFF().isEmpty()) {
            return visit(ctx.implication(0));
        }

        // Per gestire catene di biimplicazioni: A <-> B <-> C
        List<Formula> andOperands = new ArrayList<>();

        for (int i = 0; i < ctx.implication().size() - 1; i++) {
            Formula left = visit(ctx.implication(i));
            Formula right = visit(ctx.implication(i + 1));

            // A <-> B equivale a (A -> B) & (B -> A)
            // ovvero (!A | B) & (!B | A)

            // (!A | B)
            List<Formula> leftToRightOr = new ArrayList<>();
            leftToRightOr.add(new Formula(left));  // !A
            leftToRightOr.add(right);             // B
            Formula leftToRight = new Formula(Formula.Type.OR, leftToRightOr);

            // (!B | A)
            List<Formula> rightToLeftOr = new ArrayList<>();
            rightToLeftOr.add(new Formula(right));  // !B
            rightToLeftOr.add(left);              // A
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
        orOperands.add(new Formula(left));  // !A
        orOperands.add(right);            // B

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