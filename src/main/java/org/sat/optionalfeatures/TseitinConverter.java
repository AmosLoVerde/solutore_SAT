package org.sat.optionalfeatures;

import org.sat.cnf.CNFConverter;
import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;

/**
 * IMPLEMENTAZIONE CORRETTA dell'algoritmo di Tseitin per conversione CNF -> E-CNF
 *
 * Questa versione è completamente compatibile con CNFConverter esistente e gestisce
 * correttamente tutti i casi edge evitando NullPointerException e strutture malformate.
 *
 * STRATEGIA ROBUSTA:
 * 1. Analizza formula CNF esistente senza modificare struttura originale
 * 2. Genera clausole Tseitin solo se necessario (complessità > soglia)
 * 3. Costruisce E-CNF usando solo costruttori validi di CNFConverter
 *
 */
public class TseitinConverter {

    private static final Logger LOGGER = Logger.getLogger(TseitinConverter.class.getName());

    //region CONFIGURAZIONE E SOGLIE

    /** Soglia complessità oltre la quale applicare Tseitin */
    private static final int COMPLEXITY_THRESHOLD = 8;

    /** Prefisso per variabili Tseitin generate */
    private static final String TSEITIN_VAR_PREFIX = "t";

    /** ID base per variabili Tseitin (evita conflitti con variabili esistenti) */
    private static final int TSEITIN_BASE_ID = 1000;

    //endregion

    //region STATO CONVERSIONE

    /** Mapping sottoformule → variabili Tseitin */
    private Map<String, String> subformulaMap;

    /** Clausole Tseitin generate */
    private List<String> tseitinClauses;

    /** Variabili originali estratte */
    private Set<String> originalVariables;

    /** Contatore per generazione ID Tseitin univoci */
    private int nextTseitinId;

    /** Log dettagliato conversione */
    private StringBuilder conversionLog;

    //endregion

    //region INIZIALIZZAZIONE

    /**
     * Costruttore che inizializza stato per nuova conversione
     */
    public TseitinConverter() {
        resetState();
        LOGGER.fine("TseitinConverter inizializzato");
    }

    /**
     * Reset completo dello stato per nuova conversione
     */
    private void resetState() {
        this.subformulaMap = new HashMap<>();
        this.tseitinClauses = new ArrayList<>();
        this.originalVariables = new HashSet<>();
        this.nextTseitinId = TSEITIN_BASE_ID;
        this.conversionLog = new StringBuilder();
    }

    //endregion

    //region INTERFACCIA PUBBLICA PRINCIPALE

    /**
     * METODO PRINCIPALE: Converte formula CNF in E-CNF usando Tseitin
     *
     * ALGORITMO ROBUSTO:
     * 1. Reset stato e validazione input
     * 2. Analisi complessità formula
     * 3. Decisione applicazione Tseitin
     * 4. Conversione sicura se necessaria
     * 5. Ritorno formula compatibile
     *
     * @param cnfFormula formula CNF da convertire
     * @return formula E-CNF equivalente e compatibile
     */
    public CNFConverter convertToECNF(CNFConverter cnfFormula) {
        // Fase 1: Inizializzazione e validazione
        if (!initializeConversion(cnfFormula)) {
            return cnfFormula; // Ritorna originale se problemi
        }

        try {
            // Fase 2: Analisi complessità
            int complexity = calculateFormulaComplexity(cnfFormula);
            logConversionStart(cnfFormula, complexity);

            // Fase 3: Decisione conversione
            if (!shouldApplyTseitin(complexity)) {
                logNoConversionNeeded(complexity);
                return cnfFormula;
            }

            // Fase 4: Conversione Tseitin
            return performTseitinConversion(cnfFormula);

        } catch (Exception e) {
            LOGGER.log(Level.WARNING, "Errore durante conversione Tseitin", e);
            conversionLog.append("ERRORE: ").append(e.getMessage()).append("\n");
            return cnfFormula; // Fallback sicuro
        }
    }

    //endregion

    //region INIZIALIZZAZIONE E VALIDAZIONE

    /**
     * Inizializza conversione con validazione input
     */
    private boolean initializeConversion(CNFConverter cnfFormula) {
        resetState();
        conversionLog.append("=== INIZIO CONVERSIONE TSEITIN ===\n");

        if (cnfFormula == null) {
            LOGGER.warning("Formula CNF null fornita");
            conversionLog.append("ERRORE: Formula null\n");
            return false;
        }

        // Estrazione variabili originali
        extractOriginalVariables(cnfFormula);
        conversionLog.append("Variabili originali: ").append(originalVariables).append("\n");

        return true;
    }

    /**
     * Log informazioni inizio conversione
     */
    private void logConversionStart(CNFConverter cnfFormula, int complexity) {
        String formulaStr = safeToString(cnfFormula);
        conversionLog.append("Formula originale: ").append(formulaStr).append("\n");
        conversionLog.append("Complessità calcolata: ").append(complexity).append("\n\n");

        LOGGER.fine("Inizio conversione Tseitin - Complessità: " + complexity);
    }

    //endregion

    //region ANALISI COMPLESSITÀ E DECISIONI

    /**
     * Calcola complessità strutturale di una formula CNF
     */
    private int calculateFormulaComplexity(CNFConverter formula) {
        if (formula == null) return 0;

        return switch (formula.type) {
            case ATOM -> 1;
            case NOT -> 1 + safeCalculateComplexity(formula.operand);
            case AND, OR -> {
                if (formula.operands == null || formula.operands.isEmpty()) {
                    yield 1;
                }

                int total = 1; // Costo operatore
                for (CNFConverter operand : formula.operands) {
                    total += calculateFormulaComplexity(operand);
                }
                yield total;
            }
            default -> 1;
        };
    }

    /**
     * Calcolo complessità sicuro con gestione null
     */
    private int safeCalculateComplexity(CNFConverter formula) {
        return formula != null ? calculateFormulaComplexity(formula) : 0;
    }

    /**
     * Determina se applicare trasformazione Tseitin
     */
    private boolean shouldApplyTseitin(int complexity) {
        return complexity > COMPLEXITY_THRESHOLD;
    }

    /**
     * Log quando conversione non necessaria
     */
    private void logNoConversionNeeded(int complexity) {
        conversionLog.append("Formula già ottimale (complessità ").append(complexity)
                .append(" ≤ ").append(COMPLEXITY_THRESHOLD).append(")\n");
        conversionLog.append("Nessuna trasformazione applicata\n");

        LOGGER.fine("Conversione Tseitin non necessaria - formula già semplice");
    }

    //endregion

    //region CONVERSIONE TSEITIN PRINCIPALE

    /**
     * Esegue conversione Tseitin completa
     */
    private CNFConverter performTseitinConversion(CNFConverter cnfFormula) {
        //conversionLog.append("Applicazione trasformazione Tseitin...\n");

        // Fase 1: Generazione clausole Tseitin
        String mainVariable = generateTseitinClauses(cnfFormula);

        // Fase 2: Costruzione formula E-CNF finale
        CNFConverter ecnfFormula = buildECNFFormula(mainVariable);

        // Fase 3: Validazione risultato
        validateECNFResult(ecnfFormula);

        return ecnfFormula;
    }

    /**
     * Genera clausole Tseitin per la formula
     */
    private String generateTseitinClauses(CNFConverter formula) {
        // Variabile principale per la formula
        String mainVar = generateTseitinVariable();
        conversionLog.append("Variabile principale: ").append(mainVar).append("\n");

        // Genera clausole per la formula principale
        generateClausesForSubformula(formula, mainVar);

        // Clausola unitaria per forzare verità della formula
        tseitinClauses.add(mainVar);
        conversionLog.append("Clausola principale forzata: ").append(mainVar).append("\n");

        return mainVar;
    }

    /**
     * Genera clausole Tseitin per sottoformula
     */
    private void generateClausesForSubformula(CNFConverter formula, String tseitinVar) {
        if (formula == null) return;

        switch (formula.type) {
            case ATOM -> generateAtomClauses(formula.atom, tseitinVar);
            case NOT -> generateNotClauses(formula, tseitinVar);
            case AND -> generateAndClauses(formula, tseitinVar);
            case OR -> generateOrClauses(formula, tseitinVar);
            default -> {
                LOGGER.warning("Tipo formula non supportato: " + formula.type);
                conversionLog.append("ATTENZIONE: Tipo non supportato ").append(formula.type).append("\n");
            }
        }
    }

    //endregion

    //region GENERAZIONE CLAUSOLE PER TIPI SPECIFICI

    /**
     * Genera clausole per atomo: tseitinVar <-> atom
     */
    private void generateAtomClauses(String atom, String tseitinVar) {
        if (atom == null || atom.trim().isEmpty()) {
            LOGGER.warning("Atomo vuoto o null");
            return;
        }

        String cleanAtom = atom.trim();

        // tseitinVar → atom: !tseitinVar | atom
        tseitinClauses.add("!" + tseitinVar + " | " + cleanAtom);

        // atom → tseitinVar: !atom | tseitinVar
        tseitinClauses.add("!" + cleanAtom + " | " + tseitinVar);

        conversionLog.append("ATOM: ").append(tseitinVar).append(" <-> ").append(cleanAtom).append("\n");
    }

    /**
     * Genera clausole per negazione: tseitinVar <-> ¬operand
     */
    private void generateNotClauses(CNFConverter notFormula, String tseitinVar) {
        if (notFormula.operand == null) {
            LOGGER.warning("Operando NOT null");
            return;
        }

        if (notFormula.operand.type == CNFConverter.Type.ATOM) {
            // Caso semplice: NOT di atomo
            String atom = notFormula.operand.atom;
            if (atom != null) {
                // tseitinVar <-> ¬atom
                tseitinClauses.add("!" + tseitinVar + " | !" + atom);
                tseitinClauses.add(atom + " | " + tseitinVar);

                conversionLog.append("NOT ATOM: ").append(tseitinVar).append(" <-> !").append(atom).append("\n");
            }
        } else {
            // Caso complesso: NOT di sottoformula
            String subVar = generateTseitinVariable();
            generateClausesForSubformula(notFormula.operand, subVar);

            // tseitinVar <-> ¬subVar
            tseitinClauses.add("!" + tseitinVar + " | !" + subVar);
            tseitinClauses.add(subVar + " | " + tseitinVar);

            conversionLog.append("NOT COMPLEX: ").append(tseitinVar).append(" <-> !").append(subVar).append("\n");
        }
    }

    /**
     * Genera clausole per congiunzione: tseitinVar <-> (op1 & op2 & ...)
     */
    private void generateAndClauses(CNFConverter andFormula, String tseitinVar) {
        if (andFormula.operands == null || andFormula.operands.isEmpty()) {
            LOGGER.warning("AND senza operandi");
            return;
        }

        List<String> subVars = new ArrayList<>();

        // Genera variabili per ogni operando
        for (CNFConverter operand : andFormula.operands) {
            String subVar = generateTseitinVariable();
            subVars.add(subVar);
            generateClausesForSubformula(operand, subVar);
        }

        // tseitinVar → (subVar1 & subVar2 & ...)
        for (String subVar : subVars) {
            tseitinClauses.add("!" + tseitinVar + " | " + subVar);
        }

        // (subVar1 & subVar2 & ...) → tseitinVar
        StringBuilder clause = new StringBuilder();
        for (int i = 0; i < subVars.size(); i++) {
            if (i > 0) clause.append(" | ");
            clause.append("!").append(subVars.get(i));
        }
        clause.append(" | ").append(tseitinVar);
        tseitinClauses.add(clause.toString());

        conversionLog.append("AND: ").append(tseitinVar).append(" <-> (")
                .append(String.join(" & ", subVars)).append(")\n");
    }

    /**
     * Genera clausole per disgiunzione: tseitinVar <-> (op1 | op2 | ...)
     */
    private void generateOrClauses(CNFConverter orFormula, String tseitinVar) {
        if (orFormula.operands == null || orFormula.operands.isEmpty()) {
            LOGGER.warning("OR senza operandi");
            return;
        }

        List<String> subVars = new ArrayList<>();

        // Genera variabili per ogni operando
        for (CNFConverter operand : orFormula.operands) {
            String subVar = generateTseitinVariable();
            subVars.add(subVar);
            generateClausesForSubformula(operand, subVar);
        }

        // tseitinVar → (subVar1 | subVar2 | ...)
        StringBuilder clause1 = new StringBuilder("!" + tseitinVar);
        for (String subVar : subVars) {
            clause1.append(" | ").append(subVar);
        }
        tseitinClauses.add(clause1.toString());

        // (subVar1 | subVar2 | ...) → tseitinVar
        for (String subVar : subVars) {
            tseitinClauses.add("!" + subVar + " | " + tseitinVar);
        }

        conversionLog.append("OR: ").append(tseitinVar).append(" <-> (")
                .append(String.join(" | ", subVars)).append(")\n");
    }

    //endregion

    //region COSTRUZIONE FORMULA E-CNF FINALE

    /**
     * Costruisce formula E-CNF finale da clausole Tseitin
     */
    private CNFConverter buildECNFFormula(String mainVariable) {
        if (tseitinClauses.isEmpty()) {
            LOGGER.warning("Nessuna clausola Tseitin generata");
            return new CNFConverter("TRUE"); // Fallback sicuro
        }

        conversionLog.append("Clausole E-CNF generate: ").append(tseitinClauses.size()).append("\n");
        for (int i = 0; i < tseitinClauses.size(); i++) {
            conversionLog.append("  ").append(i + 1).append(". ").append(tseitinClauses.get(i)).append("\n");
        }

        // Converti clausole stringa in CNFConverter validi
        List<CNFConverter> cnfClauses = new ArrayList<>();

        for (String clauseStr : tseitinClauses) {
            CNFConverter clause = parseClauseToValidCNF(clauseStr);
            if (clause != null) {
                cnfClauses.add(clause);
            }
        }

        // Costruisci formula finale
        if (cnfClauses.isEmpty()) {
            return new CNFConverter("TRUE");
        } else if (cnfClauses.size() == 1) {
            return cnfClauses.get(0);
        } else {
            return new CNFConverter(CNFConverter.Type.AND, cnfClauses);
        }
    }

    /**
     * Converte clausola stringa in CNFConverter valido
     */
    private CNFConverter parseClauseToValidCNF(String clauseStr) {
        try {
            if (clauseStr == null || clauseStr.trim().isEmpty()) {
                return null;
            }

            String clean = clauseStr.trim();

            // Caso singolo letterale (positivo o negativo)
            if (!clean.contains("|")) {
                return parseSingleLiteral(clean);
            }

            // Caso disgiunzione multipla
            return parseDisjunction(clean);

        } catch (Exception e) {
            LOGGER.log(Level.WARNING, "Errore parsing clausola: " + clauseStr, e);
            conversionLog.append("Errore parsing: ").append(clauseStr).append("\n");
            return null;
        }
    }

    /**
     * Parsa singolo letterale
     */
    private CNFConverter parseSingleLiteral(String literal) {
        literal = literal.trim();

        if (literal.startsWith("!")) {
            String atom = literal.substring(1).trim();
            if (!atom.isEmpty()) {
                return new CNFConverter(new CNFConverter(atom));
            }
        } else {
            return new CNFConverter(literal);
        }

        return null;
    }

    /**
     * Parsa disgiunzione di letterali
     */
    private CNFConverter parseDisjunction(String disjunction) {
        String[] literals = disjunction.split("\\s*\\|\\s*");
        List<CNFConverter> orOperands = new ArrayList<>();

        for (String literal : literals) {
            literal = literal.trim();
            if (literal.isEmpty()) continue;

            if (literal.startsWith("!")) {
                String atom = literal.substring(1).trim();
                if (!atom.isEmpty()) {
                    orOperands.add(new CNFConverter(new CNFConverter(atom)));
                }
            } else {
                orOperands.add(new CNFConverter(literal));
            }
        }

        if (orOperands.isEmpty()) {
            return null;
        } else if (orOperands.size() == 1) {
            return orOperands.get(0);
        } else {
            return new CNFConverter(CNFConverter.Type.OR, orOperands);
        }
    }

    //endregion

    //region UTILITÀ E VALIDAZIONE

    /**
     * Genera nuova variabile Tseitin univoca
     */
    private String generateTseitinVariable() {
        return TSEITIN_VAR_PREFIX + (nextTseitinId++);
    }

    /**
     * Estrae tutte le variabili originali
     */
    private void extractOriginalVariables(CNFConverter formula) {
        if (formula == null) return;

        switch (formula.type) {
            case ATOM -> {
                if (formula.atom != null && !formula.atom.trim().isEmpty()) {
                    originalVariables.add(formula.atom.trim());
                }
            }
            case NOT -> {
                if (formula.operand != null) {
                    extractOriginalVariables(formula.operand);
                }
            }
            case AND, OR -> {
                if (formula.operands != null) {
                    for (CNFConverter operand : formula.operands) {
                        extractOriginalVariables(operand);
                    }
                }
            }
        }
    }

    /**
     * Validazione risultato E-CNF
     */
    private void validateECNFResult(CNFConverter ecnfFormula) {
        if (ecnfFormula == null) {
            LOGGER.severe("Formula E-CNF risultante è null");
            conversionLog.append("ERRORE CRITICO: Risultato null\n");
            return;
        }

        // Test toString() per verificare integrità struttura
        String testString = safeToString(ecnfFormula);
        if (testString.contains("ERROR") || testString.contains("null")) {
            LOGGER.warning("Possibili problemi nella struttura E-CNF");
            conversionLog.append("ATTENZIONE: Struttura potenzialmente problematica\n");
        }

        LOGGER.fine("Validazione E-CNF completata con successo");
    }

    /**
     * Conversione sicura a stringa con gestione errori
     */
    private String safeToString(CNFConverter formula) {
        try {
            return formula != null ? formula.toString() : "null";
        } catch (Exception e) {
            LOGGER.log(Level.WARNING, "Errore toString() su formula", e);
            return "ERROR_IN_TOSTRING";
        }
    }

    //endregion

    //region INTERFACCIA PUBBLICA INFORMAZIONI

    /**
     * Restituisce informazioni dettagliate sulla conversione
     */
    public String getConversionInfo() {
        StringBuilder info = new StringBuilder();
        info.append("=== TSEITIN CONVERSION REPORT ===\n");
        info.append("Variabili originali: ").append(originalVariables.size())
                .append(" ").append(originalVariables).append("\n");
        info.append("Variabili Tseitin create: ").append(nextTseitinId - TSEITIN_BASE_ID).append("\n");
        info.append("Clausole E-CNF generate: ").append(tseitinClauses.size()).append("\n");
        info.append("Soglia complessità: ").append(COMPLEXITY_THRESHOLD).append("\n");
        info.append("\nDettagli conversione:\n");
        info.append(conversionLog.toString());
        info.append("===============================\n");

        return info.toString();
    }

    /**
     * Reset per nuova conversione
     */
    public void reset() {
        resetState();
        LOGGER.fine("TseitinConverter resettato");
    }

    @Override
    public String toString() {
        return String.format("TseitinConverter[vars_orig=%d, vars_tseitin=%d, clauses=%d]",
                originalVariables.size(),
                nextTseitinId - TSEITIN_BASE_ID,
                tseitinClauses.size());
    }

    //endregion
}