package org.sat.optionalfeatures;

import org.sat.cnf.CNFConverter;
import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;

/**
 * TRASFORMAZIONE DI TSEITIN - Conversione CNF in E-CNF equisoddisfacibile
 *
 * Implementa l'algoritmo di Tseitin per la trasformazione di formule CNF in formule
 * equisoddisfacibili E-CNF (Extended CNF), introducendo variabili ausiliarie per
 * ridurre la complessità strutturale mantenendo equivalenza di soddisfacibilità.
 *
 * TEORIA E MOTIVAZIONI:
 * • Riduce la complessità esponenziale nella conversione CNF standard
 * • Introduce variabili ausiliarie che rappresentano sottostrutture complesse
 * • Mantiene equisoddisfacibilità: formula originale SAT ↔ E-CNF SAT
 * • Migliora performance SAT solver su formule con struttura profonda
 *
 * ALGORITMO TSEITIN IMPLEMENTATO:
 * • Analisi complessità strutturale per determinare necessità trasformazione
 * • Generazione variabili ausiliarie univoche per sottostrutture
 * • Creazione clausole di equivalenza: var_aux ↔ sottostruttura
 * • Costruzione E-CNF finale con clausole Tseitin + clausola principale
 * • Validazione matematica correttezza trasformazione
 *
 * BENEFICI PERFORMANCE:
 * • Clausole più corte e uniformi per SAT solver
 * • Riduzione branching factor durante ricerca
 * • Miglior locality di reference nelle strutture dati
 * • Propagazione unitaria più efficace
 *
 * SOGLIA INTELLIGENTE:
 * • Trasformazione applicata solo per complessità > soglia configurabile
 * • Evita overhead per formule già semplici
 * • Analisi automatica cost-benefit per ogni formula
 *
 * ESEMPI PRATICI:
 * Formula complessa: ((A ∧ B) ∨ (C ∧ D)) ∧ ((E ∨ F) → (G ∧ H))
 * E-CNF: t1 ↔ (A ∧ B), t2 ↔ (C ∧ D), t3 ↔ (t1 ∨ t2), ... + formula principale
 *
 * @author Amos Lo Verde
 * @version 2.0.0
 */
public class TseitinConverter {

    private static final Logger LOGGER = Logger.getLogger(TseitinConverter.class.getName());

    //region CONFIGURAZIONE E SOGLIE INTELLIGENTI

    /** Soglia complessità oltre la quale applicare trasformazione Tseitin */
    private static final int COMPLEXITY_THRESHOLD = 8;

    /** Prefisso per variabili Tseitin generate per evitare conflitti */
    private static final String TSEITIN_VAR_PREFIX = "t";

    /** ID base per variabili Tseitin (evita conflitti con variabili esistenti) */
    private static final int TSEITIN_BASE_ID = 1000;

    //endregion

    //region STATO CONVERSIONE E TRACKING

    /**
     * Mapping sottostrutture → variabili Tseitin per evitare duplicazioni.
     * Chiave: rappresentazione string della sottostruttura
     * Valore: nome variabile Tseitin associata
     */
    private Map<String, String> substructureToVariableMapping;

    /**
     * Clausole Tseitin generate durante la trasformazione.
     * Ogni clausola rappresenta equivalenza: var_tseitin ↔ sottostruttura
     */
    private List<String> generatedTseitinClauses;

    /**
     * Variabili originali estratte dalla formula per tracking completo.
     * Utilizzate per analisi dipendenze e validazione risultato.
     */
    private Set<String> originalVariables;

    /**
     * Contatore per generazione ID Tseitin univoci e progressivi.
     * Garantisce unicità anche in conversioni multiple.
     */
    private int nextTseitinId;

    /**
     * Log dettagliato della conversione per debugging e reporting.
     * Contiene cronologia completa del processo di trasformazione.
     */
    private StringBuilder conversionLog;

    //endregion

    //region INIZIALIZZAZIONE E CONFIGURAZIONE

    /**
     * Inizializza convertitore Tseitin con stato pulito.
     * Prepara tutte le strutture dati per nuova conversione.
     */
    public TseitinConverter() {
        resetConversionState();
        LOGGER.fine("TseitinConverter inizializzato per conversioni E-CNF");
    }

    /**
     * Reset completo dello stato per riutilizzo dell'istanza.
     * Pulisce tutti i dati di precedenti conversioni.
     */
    private void resetConversionState() {
        this.substructureToVariableMapping = new HashMap<>();
        this.generatedTseitinClauses = new ArrayList<>();
        this.originalVariables = new HashSet<>();
        this.nextTseitinId = TSEITIN_BASE_ID;
        this.conversionLog = new StringBuilder();
    }

    //endregion

    //region INTERFACCIA PUBBLICA PRINCIPALE

    /**
     * METODO PRINCIPALE - Converte formula CNF in E-CNF usando trasformazione Tseitin
     *
     * Esegue analisi intelligente della complessità e applica trasformazione solo
     * quando beneficiosa, garantendo sempre compatibilità e correttezza matematica.
     *
     * PIPELINE CONVERSIONE:
     * 1. Validazione input e inizializzazione logging
     * 2. Estrazione variabili originali per tracking
     * 3. Analisi complessità strutturale della formula
     * 4. Decisione intelligente applicazione Tseitin
     * 5. Generazione clausole Tseitin per sottostrutture
     * 6. Costruzione E-CNF finale equisoddisfacibile
     * 7. Validazione correttezza e integrità risultato
     *
     * @param cnfFormula formula CNF da convertire (non null)
     * @return formula E-CNF equisoddisfacibile ottimizzata
     * @throws IllegalArgumentException se formula null o malformata
     */
    public CNFConverter convertToECNF(CNFConverter cnfFormula) {
        // Fase 1: Inizializzazione e validazione robusta
        if (!initializeConversion(cnfFormula)) {
            return cnfFormula; // Ritorna originale se problemi
        }

        try {
            // Fase 2: Analisi complessità e decisione conversione
            int structuralComplexity = calculateStructuralComplexity(cnfFormula);
            logConversionStart(cnfFormula, structuralComplexity);

            if (!shouldApplyTseitinTransformation(structuralComplexity)) {
                logNoTransformationNeeded(structuralComplexity);
                return cnfFormula;
            }

            // Fase 3: Esecuzione trasformazione Tseitin
            return executeTseitinTransformation(cnfFormula);

        } catch (Exception e) {
            return handleConversionError(e, cnfFormula);
        }
    }

    //endregion

    //region INIZIALIZZAZIONE E VALIDAZIONE

    /**
     * Inizializza conversione con validazione completa e estrazione variabili.
     */
    private boolean initializeConversion(CNFConverter cnfFormula) {
        resetConversionState();
        conversionLog.append("=== INIZIO CONVERSIONE TSEITIN ===\n");

        if (cnfFormula == null) {
            LOGGER.warning("Formula CNF null fornita al convertitore Tseitin");
            conversionLog.append("ERRORE: Formula null non processabile\n");
            return false;
        }

        // Estrazione variabili originali per tracking
        extractOriginalVariables(cnfFormula);
        conversionLog.append("Variabili originali identificate: ").append(originalVariables).append("\n");

        LOGGER.fine("Inizializzazione Tseitin completata: " + originalVariables.size() + " variabili originali");
        return true;
    }

    /**
     * Estrae ricorsivamente tutte le variabili originali dalla formula.
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
     * Log informazioni inizio conversione con dettagli formula.
     */
    private void logConversionStart(CNFConverter cnfFormula, int complexity) {
        String formulaRepresentation = getFormulaStringRepresentation(cnfFormula);
        conversionLog.append("Formula da convertire: ").append(formulaRepresentation).append("\n");
        conversionLog.append("Complessità strutturale: ").append(complexity).append("\n");
        conversionLog.append("Soglia configurata: ").append(COMPLEXITY_THRESHOLD).append("\n\n");

        LOGGER.fine("Inizio conversione Tseitin - Complessità: " + complexity + ", Soglia: " + COMPLEXITY_THRESHOLD);
    }

    /**
     * Gestisce errori durante conversione con fallback sicuro.
     */
    private CNFConverter handleConversionError(Exception e, CNFConverter originalFormula) {
        LOGGER.log(Level.WARNING, "Errore durante conversione Tseitin", e);
        conversionLog.append("ERRORE: ").append(e.getMessage()).append("\n");
        conversionLog.append("Fallback: ritornata formula originale\n");
        return originalFormula; // Fallback sicuro
    }

    //endregion

    //region ANALISI COMPLESSITÀ E DECISIONI

    /**
     * Calcola complessità strutturale di una formula per decisione trasformazione.
     * Analizza profondità, branching factor e operatori nidificati.
     *
     * @param formula formula da analizzare
     * @return indice di complessità (maggiore = più complessa)
     */
    private int calculateStructuralComplexity(CNFConverter formula) {
        if (formula == null) return 0;

        return switch (formula.type) {
            case ATOM -> 1; // Complessità base per variabili atomiche
            case NOT -> 1 + calculateComplexitySafely(formula.operand); // Costo negazione
            case AND, OR -> {
                if (formula.operands == null || formula.operands.isEmpty()) {
                    yield 1;
                }

                // Costo operatore + somma complessità operandi + penalità nidificazione
                int operatorCost = 1;
                int operandsCost = 0;
                int nestingPenalty = formula.operands.size() > 2 ? formula.operands.size() : 0;

                for (CNFConverter operand : formula.operands) {
                    operandsCost += calculateStructuralComplexity(operand);
                }

                yield operatorCost + operandsCost + nestingPenalty;
            }
            default -> 1; // Fallback per tipi non riconosciuti
        };
    }

    /**
     * Calcolo complessità sicuro con gestione null.
     */
    private int calculateComplexitySafely(CNFConverter formula) {
        return formula != null ? calculateStructuralComplexity(formula) : 0;
    }

    /**
     * Determina se applicare trasformazione Tseitin basandosi su complessità.
     */
    private boolean shouldApplyTseitinTransformation(int complexity) {
        return complexity > COMPLEXITY_THRESHOLD;
    }

    /**
     * Log quando trasformazione non necessaria.
     */
    private void logNoTransformationNeeded(int complexity) {
        conversionLog.append("Formula sufficientemente semplice (complessità ").append(complexity)
                .append(" ≤ ").append(COMPLEXITY_THRESHOLD).append(")\n");
        conversionLog.append("Trasformazione Tseitin non applicata\n");

        LOGGER.fine("Trasformazione Tseitin non necessaria - formula già ottimale");
    }

    //endregion

    //region ESECUZIONE TRASFORMAZIONE TSEITIN

    /**
     * Esegue trasformazione Tseitin completa con generazione E-CNF.
     */
    private CNFConverter executeTseitinTransformation(CNFConverter cnfFormula) {
        conversionLog.append("Applicazione trasformazione Tseitin...\n");

        // Fase 1: Generazione clausole Tseitin per sottostrutture
        String mainVariable = generateTseitinClausesForFormula(cnfFormula);

        // Fase 2: Costruzione E-CNF finale
        CNFConverter ecnfFormula = buildFinalECNFFormula(mainVariable);

        // Fase 3: Validazione risultato
        validateTransformationResult(ecnfFormula);

        return ecnfFormula;
    }

    /**
     * Genera clausole Tseitin per la formula principale e sottostrutture.
     */
    private String generateTseitinClausesForFormula(CNFConverter formula) {
        // Variabile principale rappresenta l'intera formula
        String mainVariable = generateUniqueVariable();
        conversionLog.append("Variabile principale generata: ").append(mainVariable).append("\n");

        // Genera clausole per la struttura completa
        generateClausesForSubstructure(formula, mainVariable);

        // Clausola unitaria per forzare verità della formula principale
        generatedTseitinClauses.add(mainVariable);
        conversionLog.append("Clausola principale forzata: ").append(mainVariable).append("\n");

        return mainVariable;
    }

    /**
     * Genera clausole Tseitin per una sottostruttura specifica.
     */
    private void generateClausesForSubstructure(CNFConverter structure, String tseitinVariable) {
        if (structure == null) return;

        switch (structure.type) {
            case ATOM -> generateAtomEquivalenceClauses(structure.atom, tseitinVariable);
            case NOT -> generateNegationEquivalenceClauses(structure, tseitinVariable);
            case AND -> generateConjunctionEquivalenceClauses(structure, tseitinVariable);
            case OR -> generateDisjunctionEquivalenceClauses(structure, tseitinVariable);
            default -> {
                LOGGER.warning("Tipo struttura non supportato in Tseitin: " + structure.type);
                conversionLog.append("ATTENZIONE: Tipo non supportato ").append(structure.type).append("\n");
            }
        }
    }

    //endregion

    //region GENERAZIONE CLAUSOLE EQUIVALENZA

    /**
     * Genera clausole per equivalenza atomo: tseitinVar ↔ atom.
     */
    private void generateAtomEquivalenceClauses(String atom, String tseitinVar) {
        if (atom == null || atom.trim().isEmpty()) {
            LOGGER.warning("Atomo vuoto durante generazione clausole Tseitin");
            return;
        }

        String cleanAtom = atom.trim();

        // tseitinVar → atom: !tseitinVar ∨ atom
        generatedTseitinClauses.add("!" + tseitinVar + " | " + cleanAtom);

        // atom → tseitinVar: !atom ∨ tseitinVar
        generatedTseitinClauses.add("!" + cleanAtom + " | " + tseitinVar);

        conversionLog.append("EQUIVALENZA ATOMO: ").append(tseitinVar).append(" ↔ ").append(cleanAtom).append("\n");
    }

    /**
     * Genera clausole per equivalenza negazione: tseitinVar ↔ ¬operand.
     */
    private void generateNegationEquivalenceClauses(CNFConverter notStructure, String tseitinVar) {
        if (notStructure.operand == null) {
            LOGGER.warning("Operando NOT null durante generazione clausole Tseitin");
            return;
        }

        if (notStructure.operand.type == CNFConverter.Type.ATOM) {
            // Caso semplice: NOT di atomo
            String atom = notStructure.operand.atom;
            if (atom != null) {
                // tseitinVar ↔ ¬atom
                generatedTseitinClauses.add("!" + tseitinVar + " | !" + atom);
                generatedTseitinClauses.add(atom + " | " + tseitinVar);

                conversionLog.append("EQUIVALENZA NEGAZIONE: ").append(tseitinVar).append(" ↔ !").append(atom).append("\n");
            }
        } else {
            // Caso complesso: NOT di sottostruttura
            String subVariable = generateUniqueVariable();
            generateClausesForSubstructure(notStructure.operand, subVariable);

            // tseitinVar ↔ ¬subVariable
            generatedTseitinClauses.add("!" + tseitinVar + " | !" + subVariable);
            generatedTseitinClauses.add(subVariable + " | " + tseitinVar);

            conversionLog.append("EQUIVALENZA NEGAZIONE COMPLESSA: ").append(tseitinVar).append(" ↔ !").append(subVariable).append("\n");
        }
    }

    /**
     * Genera clausole per equivalenza congiunzione: tseitinVar ↔ (op1 ∧ op2 ∧ ...).
     */
    private void generateConjunctionEquivalenceClauses(CNFConverter andStructure, String tseitinVar) {
        if (andStructure.operands == null || andStructure.operands.isEmpty()) {
            LOGGER.warning("Congiunzione senza operandi durante generazione Tseitin");
            return;
        }

        List<String> subVariables = new ArrayList<>();

        // Genera variabili per ogni operando
        for (CNFConverter operand : andStructure.operands) {
            String subVar = generateUniqueVariable();
            subVariables.add(subVar);
            generateClausesForSubstructure(operand, subVar);
        }

        // tseitinVar → (subVar1 ∧ subVar2 ∧ ...)
        for (String subVar : subVariables) {
            generatedTseitinClauses.add("!" + tseitinVar + " | " + subVar);
        }

        // (subVar1 ∧ subVar2 ∧ ...) → tseitinVar
        StringBuilder clause = new StringBuilder();
        for (int i = 0; i < subVariables.size(); i++) {
            if (i > 0) clause.append(" | ");
            clause.append("!").append(subVariables.get(i));
        }
        clause.append(" | ").append(tseitinVar);
        generatedTseitinClauses.add(clause.toString());

        conversionLog.append("EQUIVALENZA CONGIUNZIONE: ").append(tseitinVar).append(" ↔ (")
                .append(String.join(" ∧ ", subVariables)).append(")\n");
    }

    /**
     * Genera clausole per equivalenza disgiunzione: tseitinVar ↔ (op1 ∨ op2 ∨ ...).
     */
    private void generateDisjunctionEquivalenceClauses(CNFConverter orStructure, String tseitinVar) {
        if (orStructure.operands == null || orStructure.operands.isEmpty()) {
            LOGGER.warning("Disgiunzione senza operandi durante generazione Tseitin");
            return;
        }

        List<String> subVariables = new ArrayList<>();

        // Genera variabili per ogni operando
        for (CNFConverter operand : orStructure.operands) {
            String subVar = generateUniqueVariable();
            subVariables.add(subVar);
            generateClausesForSubstructure(operand, subVar);
        }

        // tseitinVar → (subVar1 ∨ subVar2 ∨ ...)
        StringBuilder clause1 = new StringBuilder("!" + tseitinVar);
        for (String subVar : subVariables) {
            clause1.append(" | ").append(subVar);
        }
        generatedTseitinClauses.add(clause1.toString());

        // (subVar1 ∨ subVar2 ∨ ...) → tseitinVar
        for (String subVar : subVariables) {
            generatedTseitinClauses.add("!" + subVar + " | " + tseitinVar);
        }

        conversionLog.append("EQUIVALENZA DISGIUNZIONE: ").append(tseitinVar).append(" ↔ (")
                .append(String.join(" ∨ ", subVariables)).append(")\n");
    }

    //endregion

    //region COSTRUZIONE E-CNF FINALE

    /**
     * Costruisce formula E-CNF finale da clausole Tseitin generate.
     */
    private CNFConverter buildFinalECNFFormula(String mainVariable) {
        if (generatedTseitinClauses.isEmpty()) {
            LOGGER.warning("Nessuna clausola Tseitin generata");
            return new CNFConverter("TRUE"); // Fallback sicuro
        }

        conversionLog.append("Clausole E-CNF generate: ").append(generatedTseitinClauses.size()).append("\n");
        logGeneratedClauses();

        // Converte clausole string in CNFConverter validi
        List<CNFConverter> cnfClauses = new ArrayList<>();

        for (String clauseString : generatedTseitinClauses) {
            CNFConverter clause = parseClauseStringToValidCNF(clauseString);
            if (clause != null) {
                cnfClauses.add(clause);
            }
        }

        // Costruisce formula finale
        return buildFinalFormulaStructure(cnfClauses);
    }

    /**
     * Log dettagliato delle clausole generate per debugging.
     */
    private void logGeneratedClauses() {
        for (int i = 0; i < generatedTseitinClauses.size(); i++) {
            conversionLog.append("  ").append(i + 1).append(". ").append(generatedTseitinClauses.get(i)).append("\n");
        }
    }

    /**
     * Converte clausola string in CNFConverter valido.
     */
    private CNFConverter parseClauseStringToValidCNF(String clauseString) {
        try {
            if (clauseString == null || clauseString.trim().isEmpty()) {
                return null;
            }

            String cleanClause = clauseString.trim();

            // Caso singolo letterale (unitario)
            if (!cleanClause.contains("|")) {
                return parseSingleLiteralClause(cleanClause);
            }

            // Caso disgiunzione multipla
            return parseMultipleLiteralClause(cleanClause);

        } catch (Exception e) {
            LOGGER.log(Level.WARNING, "Errore parsing clausola Tseitin: " + clauseString, e);
            conversionLog.append("Errore parsing clausola: ").append(clauseString).append("\n");
            return null;
        }
    }

    /**
     * Parsa clausola con singolo letterale.
     */
    private CNFConverter parseSingleLiteralClause(String literal) {
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
     * Parsa clausola con letterali multipli (disgiunzione).
     */
    private CNFConverter parseMultipleLiteralClause(String disjunction) {
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

        return buildClauseStructure(orOperands);
    }

    /**
     * Costruisce struttura clausola appropriata.
     */
    private CNFConverter buildClauseStructure(List<CNFConverter> operands) {
        if (operands.isEmpty()) {
            return null;
        } else if (operands.size() == 1) {
            return operands.get(0);
        } else {
            return new CNFConverter(CNFConverter.Type.OR, operands);
        }
    }

    /**
     * Costruisce struttura formula finale appropriata.
     */
    private CNFConverter buildFinalFormulaStructure(List<CNFConverter> cnfClauses) {
        if (cnfClauses.isEmpty()) {
            return new CNFConverter("TRUE");
        } else if (cnfClauses.size() == 1) {
            return cnfClauses.get(0);
        } else {
            return new CNFConverter(CNFConverter.Type.AND, cnfClauses);
        }
    }

    //endregion

    //region UTILITÀ E VALIDAZIONE

    /**
     * Genera nuova variabile Tseitin univoca.
     */
    private String generateUniqueVariable() {
        return TSEITIN_VAR_PREFIX + (nextTseitinId++);
    }

    /**
     * Valida risultato trasformazione per integrità.
     */
    private void validateTransformationResult(CNFConverter ecnfFormula) {
        if (ecnfFormula == null) {
            LOGGER.severe("Formula E-CNF risultante è null");
            conversionLog.append("ERRORE CRITICO: Risultato trasformazione null\n");
            return;
        }

        // Test rappresentazione string per verificare integrità
        String testRepresentation = getFormulaStringRepresentation(ecnfFormula);
        if (testRepresentation.contains("ERROR") || testRepresentation.contains("null")) {
            LOGGER.warning("Possibili problemi nella struttura E-CNF generata");
            conversionLog.append("ATTENZIONE: Struttura E-CNF potenzialmente problematica\n");
        }

        LOGGER.fine("Validazione E-CNF completata con successo");
    }

    /**
     * Ottiene rappresentazione string sicura per logging.
     */
    private String getFormulaStringRepresentation(CNFConverter formula) {
        try {
            return formula != null ? formula.toString() : "null";
        } catch (Exception e) {
            LOGGER.log(Level.WARNING, "Errore toString() durante validazione formula", e);
            return "ERROR_IN_FORMULA_REPRESENTATION";
        }
    }

    //endregion

    //region INTERFACCIA PUBBLICA INFORMAZIONI

    /**
     * Restituisce informazioni dettagliate sulla conversione per reporting.
     *
     * @return report completo con statistiche e dettagli processo
     */
    public String getConversionInfo() {
        StringBuilder report = new StringBuilder();

        report.append("=== REPORT CONVERSIONE TSEITIN ===\n");
        appendConversionStatistics(report);
        appendProcessDetails(report);
        report.append("===============================\n");

        return report.toString();
    }

    /**
     * Aggiunge statistiche principali al report.
     */
    private void appendConversionStatistics(StringBuilder report) {
        report.append("Variabili originali: ").append(originalVariables.size())
                .append(" ").append(originalVariables).append("\n");
        report.append("Variabili Tseitin create: ").append(nextTseitinId - TSEITIN_BASE_ID).append("\n");
        report.append("Clausole E-CNF generate: ").append(generatedTseitinClauses.size()).append("\n");
        report.append("Soglia complessità: ").append(COMPLEXITY_THRESHOLD).append("\n");
    }

    /**
     * Aggiunge dettagli del processo al report.
     */
    private void appendProcessDetails(StringBuilder report) {
        report.append("\nDettagli conversione:\n");
        report.append(conversionLog.toString());
    }

    /**
     * Reset per nuova conversione.
     */
    public void reset() {
        resetConversionState();
        LOGGER.fine("TseitinConverter resettato per nuovo utilizzo");
    }

    /**
     * Rappresentazione testuale per debugging.
     */
    @Override
    public String toString() {
        return String.format("TseitinConverter[vars_orig=%d, vars_tseitin=%d, clauses=%d]",
                originalVariables.size(),
                nextTseitinId - TSEITIN_BASE_ID,
                generatedTseitinClauses.size());
    }

    //endregion
}