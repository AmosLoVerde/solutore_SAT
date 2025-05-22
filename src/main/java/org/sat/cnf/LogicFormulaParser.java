package org.sat.cnf;

import org.sat.antlr.org.sat.parser.LogicFormulaBaseVisitor;

import java.util.ArrayList;
import java.util.List;
import java.util.logging.Logger;

/**
 * Convertitore per trasformare l'albero di parsing delle formule logiche in oggetti CNFConverter.
 * Implementa un visitor per l'albero di parsing generato dalla grammatica LogicFormula.
 *
 */
public class LogicFormulaParser extends LogicFormulaBaseVisitor<CNFConverter> {

    /** Logger per la registrazione dei messaggi */
    private static final Logger LOGGER = Logger.getLogger(LogicFormulaParser.class.getName());

    /**
     * Punto di ingresso per la conversione di una formula in CNF.
     * Visita l'intera formula e restituisce la rappresentazione CNF.
     *
     * @param ctx contesto della formula completa
     * @return formula in CNF
     */
    @Override
    public CNFConverter visitFormula(org.sat.antlr.org.sat.parser.LogicFormulaParser.FormulaContext ctx) {
        CNFConverter formula = visit(ctx.biconditional());
        LOGGER.info("Sono qui: " + formula.toString());         // TODO: elimina
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
    public CNFConverter visitIff(org.sat.antlr.org.sat.parser.LogicFormulaParser.IffContext ctx) {
        // Se non ci sono operatori IFF, si procede con l'implicazione
        if (ctx.IFF().isEmpty()) {
            return visit(ctx.implication(0));
        }

        // Per gestire catene di doppie implicazioni: A <-> B <-> C
        List<CNFConverter> andOperands = new ArrayList<>();

        for (int i = 0; i < ctx.implication().size() - 1; i++) {
            CNFConverter left = visit(ctx.implication(i));
            CNFConverter right = visit(ctx.implication(i + 1));

            // A <-> B equivale a (A -> B) & (B -> A)
            // ovvero (!A | B) & (!B | A)

            // (!A | B)
            List<CNFConverter> leftToRightOr = new ArrayList<>();
            leftToRightOr.add(new CNFConverter(left));   // !A
            leftToRightOr.add(right);               // B
            CNFConverter leftToRight = new CNFConverter(CNFConverter.Type.OR, leftToRightOr);

            // (!B | A)
            List<CNFConverter> rightToLeftOr = new ArrayList<>();
            rightToLeftOr.add(new CNFConverter(right));  // !B
            rightToLeftOr.add(left);                // A
            CNFConverter rightToLeft = new CNFConverter(CNFConverter.Type.OR, rightToLeftOr);

            andOperands.add(leftToRight);
            andOperands.add(rightToLeft);
        }

        return new CNFConverter(CNFConverter.Type.AND, andOperands);
    }

    /**
     * Gestisce la conversione dell'implicazione (IMPLIES) in CNF.
     * A -> B diventa !A | B
     *
     * @param ctx contesto dell'implicazione
     * @return formula oggetto
     */
    @Override
    public CNFConverter visitImplies(org.sat.antlr.org.sat.parser.LogicFormulaParser.ImpliesContext ctx) {
        // Se non c'è l'operatore IMPLIES, procede con la disgiunzione
        if (ctx.IMPLIES() == null) {
            return visit(ctx.disjunction());
        }

        // A -> B equivale a !A | B
        CNFConverter left = visit(ctx.disjunction());
        CNFConverter right = visit(ctx.implication());

        // Crea !A | B
        List<CNFConverter> orOperands = new ArrayList<>();
        orOperands.add(new CNFConverter(left));   // !A
        orOperands.add(right);               // B

        return new CNFConverter(CNFConverter.Type.OR, orOperands);
    }

    /**
     * Gestisce la conversione della disgiunzione (OR).
     *
     * @param ctx contesto della disgiunzione
     * @return formula oggetto
     */
    @Override
    public CNFConverter visitOr(org.sat.antlr.org.sat.parser.LogicFormulaParser.OrContext ctx) {
        // Se c'è solo una congiunzione, la visita direttamente
        if (ctx.conjunction().size() == 1) {
            return visit(ctx.conjunction(0));
        }

        List<CNFConverter> orOperands = new ArrayList<>();

        // Raccoglie tutti gli operandi OR
        for (org.sat.antlr.org.sat.parser.LogicFormulaParser.ConjunctionContext conjCtx : ctx.conjunction()) {
            orOperands.add(visit(conjCtx));
        }

        return new CNFConverter(CNFConverter.Type.OR, orOperands);
    }

    /**
     * Gestisce la conversione della congiunzione (AND).
     *
     * @param ctx contesto della congiunzione
     * @return formula oggetto
     */
    @Override
    public CNFConverter visitAnd(org.sat.antlr.org.sat.parser.LogicFormulaParser.AndContext ctx) {
        // Se c'è solo una negazione, la visita direttamente
        if (ctx.negation().size() == 1) {
            return visit(ctx.negation(0));
        }

        List<CNFConverter> andOperands = new ArrayList<>();

        // Raccoglie tutti gli operandi AND
        for (org.sat.antlr.org.sat.parser.LogicFormulaParser.NegationContext negCtx : ctx.negation()) {
            andOperands.add(visit(negCtx));
        }

        return new CNFConverter(CNFConverter.Type.AND, andOperands);
    }

    /**
     * Gestisce la conversione della negazione (NOT).
     *
     * @param ctx contesto della negazione
     * @return formula oggetto
     */
    @Override
    public CNFConverter visitNot(org.sat.antlr.org.sat.parser.LogicFormulaParser.NotContext ctx) {
        CNFConverter innerFormula = visit(ctx.negation());
        return new CNFConverter(innerFormula);
    }

    /**
     * Gestisce la visita di una variabile.
     *
     * @param ctx contesto della variabile
     * @return formula oggetto
     */
    @Override
    public CNFConverter visitVar(org.sat.antlr.org.sat.parser.LogicFormulaParser.VarContext ctx) {
        return visit(ctx.atom());
    }

    /**
     * Gestisce la visita di espressioni in parentesi.
     *
     * @param ctx contesto delle parentesi
     * @return formula oggetto
     */
    @Override
    public CNFConverter visitPar(org.sat.antlr.org.sat.parser.LogicFormulaParser.ParContext ctx) {
        return visit(ctx.biconditional());
    }

    /**
     * Gestisce la visita di un identificatore.
     *
     * @param ctx contesto dell'identificatore
     * @return formula oggetto
     */
    @Override
    public CNFConverter visitId(org.sat.antlr.org.sat.parser.LogicFormulaParser.IdContext ctx) {
        return new CNFConverter(ctx.IDENTIFIER().getText());
    }

    /**
     * Gestisce la visita della costante TRUE.
     *
     * @param ctx contesto della costante TRUE
     * @return formula oggetto
     */
    @Override
    public CNFConverter visitTrue(org.sat.antlr.org.sat.parser.LogicFormulaParser.TrueContext ctx) {
        return new CNFConverter("TRUE");
    }

    /**
     * Gestisce la visita della costante FALSE.
     *
     * @param ctx contesto della costante FALSE
     * @return formula oggetto
     */
    @Override
    public CNFConverter visitFalse(org.sat.antlr.org.sat.parser.LogicFormulaParser.FalseContext ctx) {
        return new CNFConverter("FALSE");
    }
}