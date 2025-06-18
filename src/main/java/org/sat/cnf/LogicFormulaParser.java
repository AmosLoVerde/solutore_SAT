package org.sat.cnf;

import org.sat.antlr.org.sat.parser.LogicFormulaBaseVisitor;
import org.sat.antlr.org.sat.parser.LogicFormulaParser.FormulaContext;
import org.sat.antlr.org.sat.parser.LogicFormulaParser.IffContext;
import org.sat.antlr.org.sat.parser.LogicFormulaParser.ImpliesContext;
import org.sat.antlr.org.sat.parser.LogicFormulaParser.OrContext;
import org.sat.antlr.org.sat.parser.LogicFormulaParser.AndContext;
import org.sat.antlr.org.sat.parser.LogicFormulaParser.NotContext;
import org.sat.antlr.org.sat.parser.LogicFormulaParser.VarContext;
import org.sat.antlr.org.sat.parser.LogicFormulaParser.ParContext;
import org.sat.antlr.org.sat.parser.LogicFormulaParser.IdContext;
import org.sat.antlr.org.sat.parser.LogicFormulaParser.TrueContext;
import org.sat.antlr.org.sat.parser.LogicFormulaParser.FalseContext;

import java.util.ArrayList;
import java.util.List;
import java.util.logging.Logger;

/**
 * PARSER FORMULE LOGICHE - Convertitore da albero sintattico ANTLR a CNFConverter
 *
 * Implementa un visitor pattern per trasformare l'albero di parsing generato dalla
 * grammatica LogicFormula in strutture CNFConverter, gestendo tutti gli operatori
 * della logica proposizionale con precedenze e associatività corrette.
 *
 * OPERATORI SUPPORTATI (in ordine di precedenza crescente):
 * - Biimplicazione (<->): A <-> B ~ (A -> B) & (B -> A)
 * - Implicazione (->): A -> B ~ !A | B
 * - Disgiunzione (|): OR logico, associativo a sinistra
 * - Congiunzione (&): AND logico, associativo a sinistra
 * - Negazione (!): NOT logico, associativo a destra
 * - Variabili atomiche: identificatori e costanti logiche
 *
 * TRASFORMAZIONI SEMANTICHE:
 * - Elimina implicazioni e biimplicazioni convertendole in AND/OR/NOT
 * - Gestisce catene di operatori (A <-> B <-> C, A -> B -> C)
 * - Preserva precedenze degli operatori secondo standard logici
 * - Converte costanti logiche (TRUE/FALSE) in rappresentazioni appropriate
 *
 * ARCHITETTURA VISITOR:
 * - Pattern visitor per attraversamento albero sintattico
 * - Ogni metodo visit gestisce un costrutto grammaticale specifico
 * - Conversione bottom-up: foglie -> radice
 * - Costruzione incrementale strutture CNFConverter
 *
 * UTILIZZO TIPICO:
 * - Input: ParseTree da ANTLR parser
 * - Processing: Traversal visitor con conversioni semantiche
 * - Output: CNFConverter tree pronto per toCNF()
 * - Integration: Ponte tra parsing testuale ed elaborazione logica
 */
public class LogicFormulaParser extends LogicFormulaBaseVisitor<CNFConverter> {

    private static final Logger LOGGER = Logger.getLogger(LogicFormulaParser.class.getName());

    //region PUNTO DI INGRESSO E COORDINAMENTO PRINCIPALE

    /**
     * METODO PRINCIPALE - Punto di ingresso per conversione formula completa
     *
     * Coordina l'intero processo di conversione da albero sintattico ANTLR
     * a struttura CNFConverter, applicando automaticamente conversione CNF finale.
     *
     * PIPELINE COMPLETA:
     * 1. Traversal visitor dell'albero sintattico (biconditional root)
     * 2. Conversione semantica operatori logici in strutture CNFConverter
     * 3. Applicazione automatica conversione CNF finale
     * 4. Logging risultato per debugging e audit
     *
     * @param ctx contesto della formula completa dalla grammatica ANTLR
     * @return formula convertita in forma CNF pronta per elaborazione SAT
     */
    @Override
    public CNFConverter visitFormula(FormulaContext ctx) {
        LOGGER.fine("Inizio conversione formula da albero sintattico ANTLR");

        // Traversal partendo dal nodo biconditional (precedenza più bassa)
        CNFConverter parsedFormula = visit(ctx.biconditional());

        // Conversione automatica in CNF per output standardizzato
        CNFConverter cnfFormula = parsedFormula.toCNF();

        LOGGER.info("Formula convertita in CNF: " + cnfFormula.toString());
        return cnfFormula;
    }

    //endregion

    //region GESTIONE BIIMPLICAZIONI (PRECEDENZA PIÙ BASSA)

    /**
     * Gestisce biimplicazioni (<->) con semantica matematica rigorosa.
     *
     * SEMANTICA BIIMPLICAZIONE:
     * - A <-> B ~ (A -> B) & (B -> A)
     * - A <-> B ~ (!A | B) & (!B | A)
     * - Operatore simmetrico: A <-> B ~ B <-> A
     *
     * GESTIONE CATENE:
     * - A <-> B <-> C ~ (A <-> B) & (B <-> C)
     * - Espansione sequenziale per catene multiple
     * - Associatività gestita attraverso iterazione sistematica
     *
     * @param ctx contesto biimplicazione dalla grammatica
     * @return struttura CNFConverter rappresentante la biimplicazione espansa
     */
    @Override
    public CNFConverter visitIff(IffContext ctx) {
        // Caso base: nessun operatore IFF presente
        if (ctx.IFF().isEmpty()) {
            return visit(ctx.implication(0));
        }

        LOGGER.fine("Elaborazione catena biimplicazioni: " + ctx.IFF().size() + " operatori");

        // Gestione catene: A <-> B <-> C -> (A <-> B) & (B <-> C)
        List<CNFConverter> biimplicationClauses = new ArrayList<>();

        for (int i = 0; i < ctx.implication().size() - 1; i++) {
            CNFConverter leftOperand = visit(ctx.implication(i));
            CNFConverter rightOperand = visit(ctx.implication(i + 1));

            // Espansione A <-> B in (A -> B) & (B -> A)
            CNFConverter expandedBiimplication = expandBiimplication(leftOperand, rightOperand);
            biimplicationClauses.add(expandedBiimplication);
        }

        return buildConjunctionFromClauses(biimplicationClauses);
    }

    /**
     * Espande singola biimplicazione A <-> B in forma CNF-friendly.
     */
    private CNFConverter expandBiimplication(CNFConverter left, CNFConverter right) {
        // A <-> B ~ (A -> B) & (B -> A) ~ (!A | B) & (!B | A)

        // Direzione 1: A -> B ~ !A | B
        List<CNFConverter> leftToRightOperands = new ArrayList<>();
        leftToRightOperands.add(new CNFConverter(left));   // !A
        leftToRightOperands.add(right);                     // B
        CNFConverter leftToRight = new CNFConverter(CNFConverter.Type.OR, leftToRightOperands);

        // Direzione 2: B -> A ~ !B | A
        List<CNFConverter> rightToLeftOperands = new ArrayList<>();
        rightToLeftOperands.add(new CNFConverter(right));  // !B
        rightToLeftOperands.add(left);                      // A
        CNFConverter rightToLeft = new CNFConverter(CNFConverter.Type.OR, rightToLeftOperands);

        // Congiunzione finale: (!A | B) & (!B | A)
        List<CNFConverter> biimplicationOperands = new ArrayList<>();
        biimplicationOperands.add(leftToRight);
        biimplicationOperands.add(rightToLeft);

        return new CNFConverter(CNFConverter.Type.AND, biimplicationOperands);
    }

    //endregion

    //region GESTIONE IMPLICAZIONI (PRECEDENZA MEDIA-BASSA)

    /**
     * Gestisce implicazioni (->) con conversione in forma OR equivalente.
     *
     * SEMANTICA IMPLICAZIONE:
     * - A -> B ~ !A | B
     * - Falso solo quando A vero e B falso
     * - Associatività a destra: A -> B -> C ~ A -> (B -> C)
     *
     * GESTIONE CATENE:
     * - A -> B -> C elaborata ricorsivamente
     * - Precedenza rispetto a disgiunzione preservata
     * - Conversione diretta senza passaggi intermedi
     *
     * @param ctx contesto implicazione dalla grammatica
     * @return struttura CNFConverter rappresentante l'implicazione convertita
     */
    @Override
    public CNFConverter visitImplies(ImpliesContext ctx) {
        // Caso base: nessun operatore IMPLIES presente
        if (ctx.IMPLIES() == null) {
            return visit(ctx.disjunction());
        }

        LOGGER.fine("Elaborazione implicazione con conversione semantica");

        // A -> B ~ !A | B
        CNFConverter antecedent = visit(ctx.disjunction());     // A
        CNFConverter consequent = visit(ctx.implication());     // B (ricorsivo per associatività destra)

        // Costruzione !A | B
        List<CNFConverter> implicationOperands = new ArrayList<>();
        implicationOperands.add(new CNFConverter(antecedent));  // !A
        implicationOperands.add(consequent);                    // B

        return new CNFConverter(CNFConverter.Type.OR, implicationOperands);
    }

    //endregion

    //region GESTIONE DISGIUNZIONI (PRECEDENZA MEDIA)

    /**
     * Gestisce disgiunzioni (|) con supporto per operandi multipli.
     *
     * SEMANTICA DISGIUNZIONE:
     * - A | B: vero se almeno uno degli operandi è vero
     * - Operatore associativo: (A | B) | C ~ A | (B | C)
     * - Operatore commutativo: A | B ~ B | A
     *
     * OTTIMIZZAZIONI:
     * - Singolo operando: estrazione diretta senza wrapper OR
     * - Operandi multipli: costruzione lista unificata
     * - Preservazione ordine per debugging e tracciabilità
     *
     * @param ctx contesto disgiunzione dalla grammatica
     * @return struttura CNFConverter rappresentante la disgiunzione
     */
    @Override
    public CNFConverter visitOr(OrContext ctx) {
        // Caso ottimizzato: singola congiunzione senza OR
        if (ctx.conjunction().size() == 1) {
            return visit(ctx.conjunction(0));
        }

        LOGGER.fine("Elaborazione disgiunzione con " + ctx.conjunction().size() + " operandi");

        // Raccolta tutti gli operandi OR
        List<CNFConverter> disjunctionOperands = new ArrayList<>();
        for (var conjunctionCtx : ctx.conjunction()) {
            disjunctionOperands.add(visit(conjunctionCtx));
        }

        return new CNFConverter(CNFConverter.Type.OR, disjunctionOperands);
    }

    //endregion

    //region GESTIONE CONGIUNZIONI (PRECEDENZA MEDIA-ALTA)

    /**
     * Gestisce congiunzioni (&) con supporto per operandi multipli.
     *
     * SEMANTICA CONGIUNZIONE:
     * - A & B: vero solo se entrambi gli operandi sono veri
     * - Operatore associativo: (A & B) & C ~ A & (B & C)
     * - Operatore commutativo: A & B ~ B & A
     *
     * OTTIMIZZAZIONI:
     * - Singolo operando: estrazione diretta senza wrapper AND
     * - Operandi multipli: costruzione lista unificata
     * - Preservazione ordine per debugging e tracciabilità
     *
     * @param ctx contesto congiunzione dalla grammatica
     * @return struttura CNFConverter rappresentante la congiunzione
     */
    @Override
    public CNFConverter visitAnd(AndContext ctx) {
        // Caso ottimizzato: singola negazione senza AND
        if (ctx.negation().size() == 1) {
            return visit(ctx.negation(0));
        }

        LOGGER.fine("Elaborazione congiunzione con " + ctx.negation().size() + " operandi");

        // Raccolta tutti gli operandi AND
        List<CNFConverter> conjunctionOperands = new ArrayList<>();
        for (var negationCtx : ctx.negation()) {
            conjunctionOperands.add(visit(negationCtx));
        }

        return new CNFConverter(CNFConverter.Type.AND, conjunctionOperands);
    }

    //endregion

    //region GESTIONE NEGAZIONI (PRECEDENZA ALTA)

    /**
     * Gestisce negazioni (!) con conversione diretta.
     *
     * SEMANTICA NEGAZIONE:
     * - !A: vero se A è falso, falso se A è vero
     * - Operatore unario con precedenza massima
     * - Associatività a destra: !!A gestito correttamente
     *
     * PROCESSING:
     * - Conversione diretta in struttura NOT di CNFConverter
     * - Delegazione elaborazione operando a livelli inferiori
     * - Preservazione structure per successive ottimizzazioni
     *
     * @param ctx contesto negazione dalla grammatica
     * @return struttura CNFConverter rappresentante la negazione
     */
    @Override
    public CNFConverter visitNot(NotContext ctx) {
        LOGGER.finest("Elaborazione negazione unaria");

        CNFConverter negatedOperand = visit(ctx.negation());
        return new CNFConverter(negatedOperand);
    }

    //endregion

    //region GESTIONE VARIABILI E PARENTESI

    /**
     * Gestisce nodi variabile con delega trasparente.
     * Fornisce bridge tra costrutto grammaticale e elaborazione atomi.
     *
     * @param ctx contesto variabile dalla grammatica
     * @return struttura CNFConverter dell'atomo elaborato
     */
    @Override
    public CNFConverter visitVar(VarContext ctx) {
        return visit(ctx.atom());
    }

    /**
     * Gestisce espressioni parentesizzate con rimozione trasparente parentesi.
     * Preserva precedenze degli operatori senza introdurre overhead strutturale.
     *
     * @param ctx contesto parentesi dalla grammatica
     * @return struttura CNFConverter dell'espressione interna
     */
    @Override
    public CNFConverter visitPar(ParContext ctx) {
        LOGGER.finest("Rimozione parentesi trasparente");
        return visit(ctx.biconditional());
    }

    //endregion

    //region GESTIONE ATOMI E COSTANTI LOGICHE

    /**
     * Gestisce identificatori di variabili proposizionali.
     * Estrae nome variabile dal token ANTLR e crea nodo atomico.
     *
     * @param ctx contesto identificatore dalla grammatica
     * @return struttura CNFConverter per variabile atomica
     */
    @Override
    public CNFConverter visitId(IdContext ctx) {
        String variableName = ctx.IDENTIFIER().getText();
        LOGGER.finest("Elaborazione variabile atomica: " + variableName);
        return new CNFConverter(variableName);
    }

    /**
     * Gestisce costante logica TRUE.
     * Converte in rappresentazione simbolica per processing uniforme.
     *
     * @param ctx contesto costante TRUE dalla grammatica
     * @return struttura CNFConverter per costante vera
     */
    @Override
    public CNFConverter visitTrue(TrueContext ctx) {
        LOGGER.finest("Elaborazione costante logica TRUE");
        return new CNFConverter("TRUE");
    }

    /**
     * Gestisce costante logica FALSE.
     * Converte in rappresentazione simbolica per processing uniforme.
     *
     * @param ctx contesto costante FALSE dalla grammatica
     * @return struttura CNFConverter per costante falsa
     */
    @Override
    public CNFConverter visitFalse(FalseContext ctx) {
        LOGGER.finest("Elaborazione costante logica FALSE");
        return new CNFConverter("FALSE");
    }

    //endregion

    //region UTILITY METHODS E SUPPORTO

    /**
     * Costruisce congiunzione ottimizzata da lista di clausole.
     * Gestisce casi speciali per ottimizzazione strutturale.
     *
     * @param clauses lista di clausole da congiungere
     * @return struttura CNFConverter ottimizzata per la congiunzione
     */
    private CNFConverter buildConjunctionFromClauses(List<CNFConverter> clauses) {
        if (clauses.isEmpty()) {
            LOGGER.warning("Tentativo di costruire congiunzione da lista vuota");
            return new CNFConverter("TRUE"); // Congiunzione vuota è tautologia
        }

        if (clauses.size() == 1) {
            // Ottimizzazione: singola clausola non necessita wrapper AND
            return clauses.get(0);
        }

        return new CNFConverter(CNFConverter.Type.AND, clauses);
    }

    /**
     * Valida lista operandi per consistenza e correttezza.
     * Utilizzato per prevenzione errori durante costruzione strutture.
     *
     * @param operands lista operandi da validare
     * @param operatorName nome operatore per error reporting
     * @throws IllegalArgumentException se operandi non validi
     */
    private void validateOperands(List<CNFConverter> operands, String operatorName) {
        if (operands == null) {
            throw new IllegalArgumentException("Lista operandi null per operatore " + operatorName);
        }

        if (operands.isEmpty()) {
            throw new IllegalArgumentException("Lista operandi vuota per operatore " + operatorName);
        }

        if (operands.contains(null)) {
            throw new IllegalArgumentException("Operandi null trovati per operatore " + operatorName);
        }
    }

    /**
     * Logging configurabile per debugging del processo di parsing.
     * Fornisce visibility dettagliata del traversal dell'albero sintattico.
     *
     * @param operation nome operazione in corso
     * @param result risultato della conversione
     */
    private void logParsingOperation(String operation, CNFConverter result) {
        if (LOGGER.isLoggable(java.util.logging.Level.FINEST)) {
            LOGGER.finest(String.format("Operazione [%s] completata -> %s",
                    operation, result.toCompactString()));
        }
    }

    /**
     * Conta nodi dell'albero per statistiche di complessità.
     * Utilizzato per monitoring e ottimizzazione performance.
     *
     * @param node nodo radice per conteggio
     * @return numero totale di nodi nell'albero
     */
    private int countTreeNodes(CNFConverter node) {
        if (node == null) return 0;

        int count = 1; // Nodo corrente

        switch (node.type) {
            case NOT -> count += countTreeNodes(node.operand);
            case AND, OR -> {
                if (node.operands != null) {
                    for (CNFConverter operand : node.operands) {
                        count += countTreeNodes(operand);
                    }
                }
            }
            case ATOM -> { /* Caso base: solo nodo corrente */ }
        }

        return count;
    }

    /**
     * Estrae statistiche di parsing per monitoring e debugging.
     * Fornisce insights su complessità e caratteristiche della formula.
     *
     * @param result formula risultante dal parsing
     * @return stringa con statistiche formattate
     */
    private String extractParsingStatistics(CNFConverter result) {
        int nodeCount = countTreeNodes(result);
        int variableCount = result.countUniqueVariables();
        int depth = result.calculateDepth();

        return String.format("Stats[nodes=%d, vars=%d, depth=%d]",
                nodeCount, variableCount, depth);
    }

    //endregion
}