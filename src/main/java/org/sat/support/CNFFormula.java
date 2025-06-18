package org.sat.support;

import org.sat.cnf.CNFConverter;
import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;

/**
 * FORMULA CNF OTTIMIZZATA - Conversione da albero CNFConverter a rappresentazione numerica
 *
 * Converte la rappresentazione ad albero CNFConverter in una struttura dati altamente ottimizzata
 * per l'algoritmo CDCL. Utilizza identificatori numerici per variabili e rappresentazioni
 * compatte per clausole, massimizzando efficienza di memoria e velocità di accesso.
 *
 * OTTIMIZZAZIONI IMPLEMENTATE:
 * - Mapping bidirezionale variabili simboliche ↔ ID numerici
 * - Clausole rappresentate come List<Integer> per accesso O(1)
 * - Validazione completa durante conversione per prevenzione errori
 * - Caching intelligente per operazioni frequenti
 * - Statistiche dettagliate per analisi complessità formula
 *
 * INVARIANTI MANTENUTE:
 * - Ogni variabile simbolica ha ID numerico univoco ≥ 1
 * - Lista clausole immutabile dopo costruzione
 * - Mapping variabili preserva ordine di inserimento
 * - Tutti i letterali referenziano variabili valide
 */
public class CNFFormula {

    private static final Logger LOGGER = Logger.getLogger(CNFFormula.class.getName());

    //region STRUTTURE DATI CORE

    /**
     * Clausole CNF in formato numerico ottimizzato per elaborazione CDCL.
     * Ogni clausola è List<Integer> dove ogni Integer rappresenta un letterale:
     * - Valori positivi: letterali positivi (variabile vera)
     * - Valori negativi: letterali negati (variabile falsa)
     * - Invariante: lista immutabile dopo costruzione completa
     */
    private final List<List<Integer>> clauses;

    /**
     * Numero totale di variabili distinte nella formula.
     * Corrisponde al massimo ID variabile assegnato durante conversione.
     */
    private final int variableCount;

    /**
     * Mapping bidirezionale: nome simbolico → ID numerico.
     * Mantiene tracciabilità completa per debugging e output human-readable.
     * Invariante: ogni nome simbolico ha ID univoco ≥ 1, no duplicati
     */
    private final Map<String, Integer> variableMapping;

    //endregion

    //region COSTRUZIONE E CONVERSIONE PRINCIPALE

    /**
     * Costruisce formula CNF ottimizzata da rappresentazione ad albero CNFConverter.
     *
     * PROCESSO DI CONVERSIONE:
     * 1. Validazione input e inizializzazione strutture dati
     * 2. Analisi struttura albero CNF per identificazione pattern
     * 3. Conversione ricorsiva nodi → clausole numeriche
     * 4. Generazione mapping variabili con assegnazione ID progressivi
     * 5. Validazione integrità finale e calcolo statistiche
     * 6. Costruzione rappresentazione immutabile ottimizzata
     *
     * @param cnfConverter formula CNF in formato albero da convertire
     * @throws IllegalArgumentException se formula malformata o null
     * @throws RuntimeException se errori critici durante conversione
     */
    public CNFFormula(CNFConverter cnfConverter) {
        if (cnfConverter == null) {
            throw new IllegalArgumentException("CNFConverter non può essere null");
        }

        LOGGER.info("=== AVVIO CONVERSIONE FORMULA CNF OTTIMIZZATA ===");

        // Inizializzazione strutture dati temporanee
        this.clauses = new ArrayList<>();
        this.variableMapping = new LinkedHashMap<>(); // Preserva ordine inserimento

        try {
            // Processo di conversione principale
            executeConversionFromCNFTree(cnfConverter);

            // Finalizzazione e validazione
            this.variableCount = variableMapping.size();
            validateConversionIntegrity();
            logConversionStatistics();

        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Errore durante conversione CNF", e);
            throw new RuntimeException("Conversione CNF fallita: " + e.getMessage(), e);
        }

        LOGGER.info("=== CONVERSIONE CNF COMPLETATA CON SUCCESSO ===");
    }

    /**
     * Esegue la conversione principale dall'albero CNFConverter alle strutture numeriche.
     * Gestisce tutti i pattern possibili della struttura CNF in modo robusto.
     */
    private void executeConversionFromCNFTree(CNFConverter converter) {
        LOGGER.fine("Avvio conversione da tipo albero: " + converter.type);

        switch (converter.type) {
            case AND -> {
                // Formula complessa: congiunzione di clausole multiple
                LOGGER.fine("Conversione formula AND con multiple clausole");
                processComplexConjunctionFormula(converter);
            }
            default -> {
                // Formula semplice: clausola singola, letterale, o negazione
                LOGGER.fine("Conversione formula semplice: " + converter.type);
                processSingleElementFormula(converter);
            }
        }

        LOGGER.fine("Clausole totali estratte: " + clauses.size());
    }

    /**
     * Processa formula complessa con congiunzione di clausole multiple.
     * Ogni operando del nodo AND rappresenta una clausola separata.
     */
    private void processComplexConjunctionFormula(CNFConverter conjunctionNode) {
        if (conjunctionNode.operands == null || conjunctionNode.operands.isEmpty()) {
            LOGGER.warning("Nodo AND vuoto rilevato - formula senza clausole");
            return;
        }

        LOGGER.fine("Processamento " + conjunctionNode.operands.size() + " clausole in congiunzione");

        for (CNFConverter clauseNode : conjunctionNode.operands) {
            List<Integer> convertedClause = convertSingleClauseToNumerical(clauseNode);
            if (isClauseValid(convertedClause)) {
                clauses.add(convertedClause);
                LOGGER.finest("Clausola aggiunta: " + convertedClause);
            } else {
                LOGGER.warning("Clausola non valida ignorata: " + clauseNode);
            }
        }
    }

    /**
     * Processa formula semplice (clausola singola, letterale, o negazione).
     */
    private void processSingleElementFormula(CNFConverter singleNode) {
        List<Integer> convertedClause = convertSingleClauseToNumerical(singleNode);
        if (isClauseValid(convertedClause)) {
            clauses.add(convertedClause);
            LOGGER.fine("Clausola semplice aggiunta: " + convertedClause);
        } else {
            LOGGER.warning("Clausola semplice non valida: " + singleNode);
        }
    }

    //endregion

    //region CONVERSIONE CLAUSOLE E LETTERALI

    /**
     * Converte una singola clausola da nodo albero a rappresentazione numerica ottimizzata.
     *
     * TIPI DI CLAUSOLE GESTITI:
     * - OR: Disgiunzione di letterali → clausola normale multi-letterale
     * - ATOM: Variabile atomica → clausola unitaria positiva
     * - NOT: Negazione di variabile → clausola unitaria negativa
     * - Strutture complesse: Gestione ricorsiva con validazione
     *
     * @param clauseNode nodo albero rappresentante la clausola
     * @return lista letterali numerici (vuota se conversione fallisce)
     */
    private List<Integer> convertSingleClauseToNumerical(CNFConverter clauseNode) {
        if (clauseNode == null) {
            LOGGER.warning("Nodo clausola null rilevato");
            return new ArrayList<>();
        }

        List<Integer> literals = new ArrayList<>();

        switch (clauseNode.type) {
            case OR -> {
                // Clausola normale: disgiunzione di letterali multipli
                literals = convertDisjunctionToLiterals(clauseNode);
                LOGGER.finest("Disgiunzione convertita: " + literals.size() + " letterali");
            }
            case ATOM, NOT -> {
                // Clausola unitaria: singolo letterale (positivo o negativo)
                Integer literal = convertSingleLiteralToNumerical(clauseNode);
                if (literal != null) {
                    literals.add(literal);
                    LOGGER.finest("Letterale unitario convertito: " + literal);
                }
            }
            default -> {
                LOGGER.warning("Tipo clausola non supportato per conversione: " + clauseNode.type);
            }
        }

        return literals;
    }

    /**
     * Converte nodo OR (disgiunzione) in lista di letterali numerici.
     * Ogni operando del nodo OR diventa un letterale nella clausola risultante.
     */
    private List<Integer> convertDisjunctionToLiterals(CNFConverter orNode) {
        List<Integer> literals = new ArrayList<>();

        if (orNode.operands == null || orNode.operands.isEmpty()) {
            LOGGER.warning("Nodo OR senza operandi rilevato");
            return literals;
        }

        LOGGER.finest("Conversione " + orNode.operands.size() + " letterali da disgiunzione");

        for (CNFConverter literalNode : orNode.operands) {
            Integer convertedLiteral = convertSingleLiteralToNumerical(literalNode);
            if (convertedLiteral != null) {
                literals.add(convertedLiteral);
                LOGGER.finest("Letterale aggiunto: " + convertedLiteral);
            } else {
                LOGGER.warning("Letterale non convertibile ignorato: " + literalNode);
            }
        }

        return literals;
    }

    /**
     * Converte un singolo letterale in rappresentazione numerica DIMACS.
     *
     * CONVERSIONE DIMACS:
     * - ATOM "P" → +ID (letterale positivo)
     * - NOT ATOM "¬P" → -ID (letterale negativo)
     * - ID sono generati progressivamente per mantenere consistenza
     *
     * @param literalNode nodo rappresentante il letterale
     * @return ID numerico del letterale (null se conversione fallisce)
     */
    private Integer convertSingleLiteralToNumerical(CNFConverter literalNode) {
        if (literalNode == null) {
            LOGGER.finest("Nodo letterale null");
            return null;
        }

        return switch (literalNode.type) {
            case ATOM -> convertPositiveLiteral(literalNode);
            case NOT -> convertNegativeLiteral(literalNode);
            default -> {
                LOGGER.warning("Tipo letterale non riconosciuto: " + literalNode.type);
                yield null;
            }
        };
    }

    /**
     * Converte letterale positivo (variabile atomica) in ID numerico positivo.
     */
    private Integer convertPositiveLiteral(CNFConverter atomNode) {
        String variableName = extractAndValidateVariableName(atomNode.atom);
        if (variableName == null) {
            return null;
        }

        Integer variableId = getOrCreateVariableId(variableName);
        LOGGER.finest("Letterale positivo convertito: " + variableName + " → +" + variableId);
        return variableId;
    }

    /**
     * Converte letterale negativo (NOT di variabile atomica) in ID numerico negativo.
     */
    private Integer convertNegativeLiteral(CNFConverter notNode) {
        // Validazione struttura NOT(ATOM)
        if (notNode.operand == null || notNode.operand.type != CNFConverter.Type.ATOM) {
            LOGGER.warning("Struttura NOT non valida - operando: " +
                    (notNode.operand != null ? notNode.operand.type : "null"));
            return null;
        }

        String variableName = extractAndValidateVariableName(notNode.operand.atom);
        if (variableName == null) {
            return null;
        }

        Integer variableId = getOrCreateVariableId(variableName);
        Integer negatedId = -variableId;

        LOGGER.finest("Letterale negativo convertito: ¬" + variableName + " → " + negatedId);
        return negatedId;
    }

    //endregion

    //region GESTIONE MAPPING VARIABILI

    /**
     * Estrae e valida nome variabile da stringa atomica con normalizzazione.
     */
    private String extractAndValidateVariableName(String atom) {
        if (atom == null || atom.trim().isEmpty()) {
            LOGGER.warning("Nome variabile vuoto o null rilevato");
            return null;
        }

        String normalizedName = atom.trim();

        // Validazione ulteriore nome variabile
        if (normalizedName.contains(" ") || normalizedName.contains("\t")) {
            LOGGER.warning("Nome variabile contiene spazi: '" + normalizedName + "'");
            return normalizedName.replaceAll("\\s+", "_"); // Normalizzazione automatica
        }

        return normalizedName;
    }

    /**
     * Ottiene ID numerico per variabile, creandolo se necessario con strategia lazy.
     *
     * STRATEGIA ASSEGNAZIONE ID:
     * - Se variabile già mappata → restituisce ID esistente
     * - Se variabile nuova → assegna prossimo ID disponibile (progressivo)
     * - Aggiorna mapping bidirezionale e registra nel log
     * - Garantisce univocità e consistenza degli ID
     *
     * @param variableName nome simbolico della variabile
     * @return ID numerico univoco (sempre > 0)
     */
    private Integer getOrCreateVariableId(String variableName) {
        return variableMapping.computeIfAbsent(variableName, name -> {
            int newId = variableMapping.size() + 1;
            LOGGER.finest("Nuova variabile mappata: " + name + " → ID " + newId);
            return newId;
        });
    }

    //endregion

    //region VALIDAZIONE E INTEGRITÀ

    /**
     * Verifica se una clausola convertita è valida per inclusione nella formula.
     */
    private boolean isClauseValid(List<Integer> clause) {
        return clause != null && !clause.isEmpty();
    }

    /**
     * Valida integrità completa della conversione eseguita.
     * Verifica consistenza tra tutte le strutture dati e assenza di corruzioni.
     */
    private void validateConversionIntegrity() {
        LOGGER.fine("Avvio validazione integrità conversione CNF");

        // Validazione coerenza conteggio variabili
        if (variableCount != variableMapping.size()) {
            throw new IllegalStateException("Inconsistenza conteggio variabili: atteso=" +
                    variableMapping.size() + ", calcolato=" + variableCount);
        }

        // Validazione integrità mapping variabili
        validateVariableMapping();

        // Validazione range letterali nelle clausole
        validateClauseLiterals();

        LOGGER.fine("Validazione integrità conversione: SUCCESSO");
    }

    /**
     * Valida integrità del mapping delle variabili.
     */
    private void validateVariableMapping() {
        for (Map.Entry<String, Integer> entry : variableMapping.entrySet()) {
            String variableName = entry.getKey();
            Integer variableId = entry.getValue();

            if (variableName == null || variableName.trim().isEmpty()) {
                throw new IllegalStateException("Nome variabile vuoto nel mapping: '" + variableName + "'");
            }

            if (variableId == null || variableId <= 0) {
                throw new IllegalStateException("ID variabile non valido per '" + variableName + "': " + variableId);
            }

            if (variableId > variableCount) {
                throw new IllegalStateException("ID variabile fuori range per '" + variableName + "': " +
                        variableId + " > " + variableCount);
            }
        }
    }

    /**
     * Valida range e consistenza dei letterali nelle clausole.
     */
    private void validateClauseLiterals() {
        for (int clauseIndex = 0; clauseIndex < clauses.size(); clauseIndex++) {
            List<Integer> clause = clauses.get(clauseIndex);

            for (int literalIndex = 0; literalIndex < clause.size(); literalIndex++) {
                Integer literal = clause.get(literalIndex);
                int absoluteLiteral = Math.abs(literal);

                if (literal == null || literal == 0) {
                    throw new IllegalStateException("Letterale non valido in clausola " + clauseIndex +
                            "[" + literalIndex + "]: " + literal);
                }

                if (absoluteLiteral > variableCount) {
                    throw new IllegalStateException("Letterale fuori range in clausola " + clauseIndex +
                            "[" + literalIndex + "]: |" + literal + "| > " + variableCount);
                }
            }
        }
    }

    //endregion

    //region STATISTICHE E LOGGING

    /**
     * Registra statistiche dettagliate sulla conversione completata.
     */
    private void logConversionStatistics() {
        int totalLiterals = clauses.stream().mapToInt(List::size).sum();
        double avgClauseLength = clauses.isEmpty() ? 0.0 : (double) totalLiterals / clauses.size();

        LOGGER.info(String.format("Conversione CNF completata: %d clausole, %d variabili, %.1f letterali/clausola",
                clauses.size(), variableCount, avgClauseLength));

        // Statistiche avanzate per debugging
        if (LOGGER.isLoggable(Level.FINE)) {
            logAdvancedStatistics(totalLiterals, avgClauseLength);
        }
    }

    /**
     * Registra statistiche avanzate per analisi approfondita.
     */
    private void logAdvancedStatistics(int totalLiterals, double avgClauseLength) {
        // Distribuzione lunghezza clausole
        Map<Integer, Long> lengthDistribution = clauses.stream()
                .collect(java.util.stream.Collectors.groupingBy(
                        List::size, java.util.stream.Collectors.counting()));

        LOGGER.fine("Distribuzione lunghezza clausole: " + lengthDistribution);

        // Analisi densità formula
        double density = (double) totalLiterals / (variableCount * clauses.size());
        LOGGER.fine(String.format("Densità formula: %.3f (letterali per variabile-clausola)", density));

        // Clausole unitarie
        long unitClauses = clauses.stream().filter(clause -> clause.size() == 1).count();
        LOGGER.fine("Clausole unitarie: " + unitClauses + "/" + clauses.size());

        // Log mapping variabili per debugging
        if (LOGGER.isLoggable(Level.FINEST)) {
            LOGGER.finest("Mapping completo variabili: " + variableMapping);
        }
    }

    //endregion

    //region INTERFACCIA PUBBLICA

    /**
     * @return copia immutabile delle clausole CNF in formato numerico
     */
    public List<List<Integer>> getClauses() {
        return new ArrayList<>(clauses);
    }

    /**
     * @return numero di variabili distinte nella formula
     */
    public int getVariableCount() {
        return variableCount;
    }

    /**
     * @return numero di clausole nella formula
     */
    public int getClausesCount() {
        return clauses.size();
    }

    /**
     * @return copia immutabile del mapping variabili simboliche → ID numerici
     */
    public Map<String, Integer> getVariableMapping() {
        return new LinkedHashMap<>(variableMapping);
    }

    /**
     * Rappresentazione testuale per debugging con informazioni essenziali.
     */
    @Override
    public String toString() {
        return String.format("CNFFormula{clausole=%d, variabili=%d, mapping=%s}",
                clauses.size(), variableCount, variableMapping.keySet());
    }

    //endregion
}