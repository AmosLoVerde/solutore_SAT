// Generated from /Users/amosloverde/Desktop/bonacina/solutore_SAT/src/main/java/org/sat/antlr/org/sat/parser/LogicFormula.g4 by ANTLR 4.13.2
package org.sat.antlr.org.sat.parser;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link LogicFormulaParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface LogicFormulaVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link LogicFormulaParser#formula}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFormula(LogicFormulaParser.FormulaContext ctx);
	/**
	 * Visit a parse tree produced by the {@code iff}
	 * labeled alternative in {@link LogicFormulaParser#biconditional}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIff(LogicFormulaParser.IffContext ctx);
	/**
	 * Visit a parse tree produced by the {@code implies}
	 * labeled alternative in {@link LogicFormulaParser#implication}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitImplies(LogicFormulaParser.ImpliesContext ctx);
	/**
	 * Visit a parse tree produced by the {@code or}
	 * labeled alternative in {@link LogicFormulaParser#disjunction}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitOr(LogicFormulaParser.OrContext ctx);
	/**
	 * Visit a parse tree produced by the {@code and}
	 * labeled alternative in {@link LogicFormulaParser#conjunction}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAnd(LogicFormulaParser.AndContext ctx);
	/**
	 * Visit a parse tree produced by the {@code not}
	 * labeled alternative in {@link LogicFormulaParser#negation}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNot(LogicFormulaParser.NotContext ctx);
	/**
	 * Visit a parse tree produced by the {@code var}
	 * labeled alternative in {@link LogicFormulaParser#negation}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVar(LogicFormulaParser.VarContext ctx);
	/**
	 * Visit a parse tree produced by the {@code par}
	 * labeled alternative in {@link LogicFormulaParser#atom}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitPar(LogicFormulaParser.ParContext ctx);
	/**
	 * Visit a parse tree produced by the {@code id}
	 * labeled alternative in {@link LogicFormulaParser#atom}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitId(LogicFormulaParser.IdContext ctx);
	/**
	 * Visit a parse tree produced by the {@code true}
	 * labeled alternative in {@link LogicFormulaParser#atom}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitTrue(LogicFormulaParser.TrueContext ctx);
	/**
	 * Visit a parse tree produced by the {@code false}
	 * labeled alternative in {@link LogicFormulaParser#atom}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFalse(LogicFormulaParser.FalseContext ctx);
}