package org.sat.optionalfeatures;

import org.sat.cnf.CNFConverter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;

/**
 * CONVERTITORE CNF STANDARD - Sistema per conversione diretta da formato DIMACS
 *
 * Implementa la conversione automatica da file CNF in formato DIMACS standard
 * a strutture CNFConverter utilizzabili dal solutore CDCL. Gestisce il parsing
 * robusto del formato numerico e la mappatura automatica a variabili simboliche.
 */
public class StandardConverterCNF {

    private static final Logger LOGGER = Logger.getLogger(StandardConverterCNF.class.getName());

    //region CONFIGURAZIONE E COSTANTI

    /** Prefisso per variabili generate dalla conversione numerica */
    private static final String VARIABLE_PREFIX = "p";

    /** Terminatore clausola nel formato DIMACS */
    private static final int CLAUSE_TERMINATOR = 0;

    /** Carattere commento nel formato DIMACS */
    private static final char COMMENT_CHAR = 'c';

    /** Prefisso header problema nel formato DIMACS */
    private static final String PROBLEM_PREFIX = "p cnf";

    //endregion

    //region STATO CONVERSIONE

    /**
     * Clausole estratte dal file CNF in formato numerico.
     * Ogni clausola è rappresentata come lista di letterali con segno.
     */
    private List<List<Integer>> extractedClauses;

    /**
     * Mapping da ID numerico a nome variabile simbolica per output leggibile.
     * Esempio: 1 -> "p1", 2 -> "p2", 3 -> "p3"
     */
    private Map<Integer, String> variableMapping;

    /**
     * Set di tutte le variabili uniche trovate nel file CNF.
     * Utilizzato per validazione e costruzione mapping completo.
     */
    private Set<Integer> uniqueVariables;

    /**
     * Log dettagliato della conversione per debugging e reporting.
     * Contiene cronologia completa del processo di parsing e conversione.
     */
    private StringBuilder conversionLog;

    /**
     * Statistiche di conversione per analisi e validazione.
     */
    private ConversionStatistics statistics;

    //endregion

    //region INIZIALIZZAZIONE

    /**
     * Inizializza convertitore CNF standard con stato pulito.
     * Prepara tutte le strutture dati per nuova conversione.
     */
    public StandardConverterCNF() {
        resetConversionState();
        LOGGER.fine("StandardConverterCNF inizializzato per conversione diretta");
    }

    /**
     * Reset completo dello stato per riutilizzo dell'istanza.
     * Pulisce tutti i dati di precedenti conversioni.
     */
    private void resetConversionState() {
        this.extractedClauses = new ArrayList<>();
        this.variableMapping = new HashMap<>();
        this.uniqueVariables = new HashSet<>();
        this.conversionLog = new StringBuilder();
        this.statistics = new ConversionStatistics();
    }

    //endregion

    //region INTERFACCIA PUBBLICA PRINCIPALE

    /**
     * METODO PRINCIPALE - Converte file CNF standard in CNFConverter
     *
     * Esegue conversione completa da formato DIMACS a struttura CNFConverter
     * utilizzabile dal solutore CDCL. Gestisce automaticamente parsing,
     * validazione, mappatura variabili e costruzione struttura finale.
     *
     * PIPELINE CONVERSIONE:
     * 1. Validazione e lettura file input
     * 2. Parsing robusto con filtraggio commenti
     * 3. Estrazione e validazione clausole
     * 4. Mappatura variabili numeriche a simboliche
     * 5. Costruzione CNFConverter con struttura ottimale
     * 6. Validazione integrità e finalizzazione
     *
     * @param filePath percorso del file .cnf da convertire
     * @return CNFConverter equivalente alla formula nel file
     * @throws IOException se errori di accesso al file
     * @throws IllegalArgumentException se formato file non valido
     * @throws RuntimeException se errori critici durante conversione
     */
    public CNFConverter convertFromStandardCNF(String filePath) throws IOException {
        // Fase 1: Inizializzazione e validazione
        if (!initializeConversion(filePath)) {
            throw new IllegalArgumentException("Impossibile inizializzare conversione per: " + filePath);
        }

        try {
            // Fase 2: Lettura e parsing del file
            List<String> fileLines = readAndValidateFile(filePath);

            // Fase 3: Estrazione clausole con parsing robusto
            extractClausesFromLines(fileLines);

            // Fase 4: Mappatura variabili e validazione
            buildVariableMapping();

            // Fase 5: Costruzione CNFConverter finale
            CNFConverter result = buildCNFConverterFromClauses();

            // Fase 6: Finalizzazione e validazione
            finalizeConversionWithValidation(result);

            return result;

        } catch (Exception e) {
            return handleConversionError(e, filePath);
        }
    }

    //endregion

    //region INIZIALIZZAZIONE E VALIDAZIONE

    /**
     * Inizializza conversione con validazione completa dell'input.
     *
     * @param filePath percorso file da validare
     * @return true se inizializzazione successful, false altrimenti
     */
    private boolean initializeConversion(String filePath) {
        resetConversionState();
        conversionLog.append("=== INIZIO CONVERSIONE CNF STANDARD ===\n");

        if (filePath == null || filePath.trim().isEmpty()) {
            LOGGER.warning("Percorso file null o vuoto fornito al convertitore");
            conversionLog.append("ERRORE: Percorso file non valido\n");
            return false;
        }

        // Verifica estensione file
        if (!filePath.toLowerCase().endsWith(".cnf")) {
            LOGGER.warning("File non ha estensione .cnf: " + filePath);
            conversionLog.append("ATTENZIONE: File senza estensione .cnf\n");
        }

        conversionLog.append("File da convertire: ").append(filePath).append("\n");
        LOGGER.fine("Inizio conversione CNF standard per: " + filePath);
        return true;
    }

    /**
     * Legge e valida file CNF con gestione errori robusta.
     *
     * @param filePath percorso del file da leggere
     * @return liste di righe del file filtrate e validate
     * @throws IOException se errori di accesso al file
     */
    private List<String> readAndValidateFile(String filePath) throws IOException {
        LOGGER.fine("Lettura file CNF: " + filePath);

        Path path = Paths.get(filePath);
        if (!Files.exists(path)) {
            throw new IOException("File non esistente: " + filePath);
        }

        if (!Files.isReadable(path)) {
            throw new IOException("File non leggibile: " + filePath);
        }

        List<String> lines = Files.readAllLines(path);
        statistics.totalLines = lines.size();

        conversionLog.append("Righe totali lette: ").append(lines.size()).append("\n");
        LOGGER.fine("File letto: " + lines.size() + " righe totali");

        return lines;
    }

    /**
     * Gestisce errori durante conversione con fallback sicuro.
     */
    private CNFConverter handleConversionError(Exception e, String filePath) {
        LOGGER.log(Level.SEVERE, "Errore durante conversione CNF standard", e);
        conversionLog.append("ERRORE CRITICO: ").append(e.getMessage()).append("\n");

        // Per errori di conversione, non c'è fallback sicuro - propaga l'errore
        throw new RuntimeException("Conversione CNF fallita per file: " + filePath, e);
    }

    //endregion

    //region PARSING E ESTRAZIONE CLAUSOLE

    /**
     * Estrae clausole dalle righe del file con parsing robusto formato DIMACS.
     *
     * @param fileLines righe del file da processare
     */
    private void extractClausesFromLines(List<String> fileLines) {
        conversionLog.append("\n=== ESTRAZIONE CLAUSOLE ===\n");

        for (int lineNumber = 0; lineNumber < fileLines.size(); lineNumber++) {
            String line = fileLines.get(lineNumber);
            processLine(line, lineNumber + 1);
        }

        statistics.extractedClauses = extractedClauses.size();
        conversionLog.append("Clausole estratte: ").append(statistics.extractedClauses).append("\n");

        LOGGER.fine("Estrazione completata: " + statistics.extractedClauses + " clausole trovate");
    }

    /**
     * Processa singola riga del file CNF con gestione formato DIMACS.
     *
     * @param line riga da processare
     * @param lineNumber numero riga per error reporting
     */
    private void processLine(String line, int lineNumber) {
        // Normalizzazione riga
        String cleanLine = line.trim();

        // Filtraggio righe non rilevanti
        if (isLineToSkip(cleanLine)) {
            statistics.skippedLines++;
            return;
        }

        // Tentativo parsing clausola
        List<Integer> clause = parseClauseFromLine(cleanLine, lineNumber);
        if (clause != null && !clause.isEmpty()) {
            extractedClauses.add(clause);
            statistics.validLines++;

            // Log dettagliato per debugging
            if (LOGGER.isLoggable(Level.FINEST)) {
                LOGGER.finest("Clausola estratta da riga " + lineNumber + ": " + clause);
            }
        } else {
            statistics.invalidLines++;
            conversionLog.append("Riga ").append(lineNumber).append(" ignorata: formato non valido\n");
        }
    }

    /**
     * Determina se una riga deve essere saltata (commenti, header, vuote).
     *
     * @param line riga pulita da verificare
     * @return true se riga da saltare, false se da processare
     */
    private boolean isLineToSkip(String line) {
        if (line.isEmpty()) {
            return true; // Riga vuota
        }

        if (line.charAt(0) == COMMENT_CHAR) {
            return true; // Riga di commento
        }

        if (line.startsWith(PROBLEM_PREFIX)) {
            return true; // Header problema (p cnf variables clauses)
        }

        return false;
    }

    /**
     * Parsa clausola da riga con validazione formato DIMACS.
     *
     * @param line riga contenente clausola
     * @param lineNumber numero riga per error reporting
     * @return lista letterali della clausola, null se formato non valido
     */
    private List<Integer> parseClauseFromLine(String line, int lineNumber) {
        try {
            // Split su spazi multipli e filtraggio
            String[] tokens = line.split("\\s+");
            List<Integer> clause = new ArrayList<>();

            boolean foundTerminator = false;

            for (String token : tokens) {
                if (token.trim().isEmpty()) {
                    continue; // Salta token vuoti
                }

                int literal = Integer.parseInt(token.trim());

                if (literal == CLAUSE_TERMINATOR) {
                    foundTerminator = true;
                    break; // Fine clausola
                }

                // Aggiunge letterale valido
                clause.add(literal);

                // Registra variabile per mapping
                int variable = Math.abs(literal);
                uniqueVariables.add(variable);
            }

            // Validazione formato clausola
            if (!foundTerminator) {
                LOGGER.warning("Riga " + lineNumber + " senza terminatore 0: " + line);
                return null;
            }

            if (clause.isEmpty()) {
                LOGGER.warning("Clausola vuota alla riga " + lineNumber);
                // Clausola vuota è valida (rappresenta contraddizione)
            }

            return clause;

        } catch (NumberFormatException e) {
            LOGGER.warning("Formato numerico non valido alla riga " + lineNumber + ": " + line);
            return null;
        }
    }

    //endregion

    //region MAPPATURA VARIABILI

    /**
     * Costruisce mapping da ID numerici a nomi variabili simboliche.
     */
    private void buildVariableMapping() {
        conversionLog.append("\n=== MAPPATURA VARIABILI ===\n");

        // Ordina variabili per ID crescente
        List<Integer> sortedVariables = new ArrayList<>(uniqueVariables);
        sortedVariables.sort(Integer::compareTo);

        // Crea mapping con prefisso standard
        for (Integer variable : sortedVariables) {
            String symbolicName = VARIABLE_PREFIX + variable;
            variableMapping.put(variable, symbolicName);
        }

        statistics.uniqueVariables = uniqueVariables.size();
        conversionLog.append("Variabili uniche: ").append(statistics.uniqueVariables).append("\n");
        conversionLog.append("Mapping: ").append(variableMapping).append("\n");

        LOGGER.fine("Mapping variabili creato: " + statistics.uniqueVariables + " variabili");
    }

    //endregion

    //region COSTRUZIONE CNFCONVERTER

    /**
     * Costruisce CNFConverter da clausole estratte con struttura ottimale.
     *
     * @return CNFConverter equivalente alla formula CNF
     */
    private CNFConverter buildCNFConverterFromClauses() {
        conversionLog.append("\n=== COSTRUZIONE CNFCONVERTER ===\n");

        if (extractedClauses.isEmpty()) {
            conversionLog.append("Nessuna clausola -> formula TRUE\n");
            return new CNFConverter("TRUE");
        }

        List<CNFConverter> cnfClauses = new ArrayList<>();

        // Converte ogni clausola numerica in CNFConverter
        for (int i = 0; i < extractedClauses.size(); i++) {
            List<Integer> numericClause = extractedClauses.get(i);
            CNFConverter cnfClause = convertNumericClauseToCNF(numericClause, i + 1);

            if (cnfClause != null) {
                cnfClauses.add(cnfClause);
            }
        }

        // Costruisce struttura finale ottimale
        CNFConverter result = buildOptimalCNFStructure(cnfClauses);

        conversionLog.append("CNFConverter costruito: ").append(result.toString()).append("\n");
        LOGGER.fine("CNFConverter costruito con " + cnfClauses.size() + " clausole");

        return result;
    }

    /**
     * Converte clausola numerica in CNFConverter con nomi simbolici.
     *
     * @param numericClause clausola in formato numerico
     * @param clauseIndex indice clausola per logging
     * @return CNFConverter per la clausola
     */
    private CNFConverter convertNumericClauseToCNF(List<Integer> numericClause, int clauseIndex) {
        if (numericClause.isEmpty()) {
            // Clausola vuota rappresenta contraddizione
            conversionLog.append("Clausola ").append(clauseIndex).append(": [] (vuota)\n");
            return new CNFConverter("FALSE");
        }

        List<CNFConverter> literals = new ArrayList<>();

        // Converte ogni letterale numerico
        for (Integer literal : numericClause) {
            CNFConverter cnfLiteral = convertNumericLiteralToCNF(literal);
            if (cnfLiteral != null) {
                literals.add(cnfLiteral);
            }
        }

        CNFConverter clause = buildClauseStructure(literals);

        // Log dettagliato per debugging
        conversionLog.append("Clausola ").append(clauseIndex).append(": ")
                .append(numericClause).append(" -> ").append(clause.toString()).append("\n");

        return clause;
    }

    /**
     * Converte letterale numerico in CNFConverter simbolico.
     *
     * @param literal letterale numerico (positivo o negativo)
     * @return CNFConverter per il letterale
     */
    private CNFConverter convertNumericLiteralToCNF(Integer literal) {
        int variable = Math.abs(literal);
        String symbolicName = variableMapping.get(variable);

        if (symbolicName == null) {
            LOGGER.warning("Variabile non mappata: " + variable);
            symbolicName = VARIABLE_PREFIX + variable; // Fallback
        }

        if (literal > 0) {
            // Letterale positivo
            return new CNFConverter(symbolicName);
        } else {
            // Letterale negativo
            return new CNFConverter(new CNFConverter(symbolicName));
        }
    }

    /**
     * Costruisce struttura clausola ottimale basata su numero letterali.
     *
     * @param literals lista letterali della clausola
     * @return CNFConverter ottimale per la clausola
     */
    private CNFConverter buildClauseStructure(List<CNFConverter> literals) {
        if (literals.isEmpty()) {
            return new CNFConverter("FALSE"); // Clausola vuota
        } else if (literals.size() == 1) {
            return literals.get(0); // Clausola unitaria
        } else {
            return new CNFConverter(CNFConverter.Type.OR, literals); // Disgiunzione
        }
    }

    /**
     * Costruisce struttura CNF finale ottimale.
     *
     * @param cnfClauses lista clausole CNFConverter
     * @return CNFConverter finale ottimale
     */
    private CNFConverter buildOptimalCNFStructure(List<CNFConverter> cnfClauses) {
        if (cnfClauses.isEmpty()) {
            return new CNFConverter("TRUE"); // Formula vuota
        } else if (cnfClauses.size() == 1) {
            return cnfClauses.get(0); // Singola clausola
        } else {
            return new CNFConverter(CNFConverter.Type.AND, cnfClauses); // Congiunzione
        }
    }

    //endregion

    //region FINALIZZAZIONE E VALIDAZIONE

    /**
     * Finalizza conversione con validazione completa del risultato.
     *
     * @param result CNFConverter risultante dalla conversione
     */
    private void finalizeConversionWithValidation(CNFConverter result) {
        conversionLog.append("\n=== FINALIZZAZIONE CONVERSIONE ===\n");

        // Validazione integrità risultato
        validateConversionResult(result);

        // Generazione statistiche finali
        generateFinalStatistics();

        // Log riepilogo
        conversionLog.append("Conversione completata con successo\n");
        conversionLog.append("Formula finale: ").append(result.toString()).append("\n");

        LOGGER.info("Conversione CNF standard completata: " +
                statistics.extractedClauses + " clausole, " +
                statistics.uniqueVariables + " variabili");
    }

    /**
     * Valida integrità del risultato di conversione.
     *
     * @param result CNFConverter da validare
     */
    private void validateConversionResult(CNFConverter result) {
        if (result == null) {
            throw new IllegalStateException("Risultato conversione è null");
        }

        // Test rappresentazione string per verificare integrità
        try {
            String representation = result.toString();
            if (representation.contains("null") || representation.contains("ERROR")) {
                LOGGER.warning("Possibili problemi nella struttura CNF convertita");
            }
        } catch (Exception e) {
            LOGGER.warning("Errore validazione rappresentazione CNF: " + e.getMessage());
        }

        LOGGER.fine("Validazione risultato conversione: SUCCESSO");
    }

    /**
     * Genera statistiche finali per reporting e analisi.
     */
    private void generateFinalStatistics() {
        conversionLog.append("\n=== STATISTICHE CONVERSIONE ===\n");
        conversionLog.append("Righe totali: ").append(statistics.totalLines).append("\n");
        conversionLog.append("Righe saltate: ").append(statistics.skippedLines).append("\n");
        conversionLog.append("Righe valide: ").append(statistics.validLines).append("\n");
        conversionLog.append("Righe invalide: ").append(statistics.invalidLines).append("\n");
        conversionLog.append("Clausole estratte: ").append(statistics.extractedClauses).append("\n");
        conversionLog.append("Variabili uniche: ").append(statistics.uniqueVariables).append("\n");

        if (statistics.totalLines > 0) {
            double validPercentage = (double) statistics.validLines / statistics.totalLines * 100;
            conversionLog.append("Percentuale righe valide: ").append(String.format("%.1f%%", validPercentage)).append("\n");
        }
    }

    //endregion

    //region INTERFACCIA PUBBLICA INFORMAZIONI

    /**
     * Restituisce log dettagliato della conversione per debugging.
     *
     * @return stringa con cronologia completa della conversione
     */
    public String getConversionLog() {
        return conversionLog.toString();
    }

    /**
     * Restituisce statistiche della conversione per analisi.
     *
     * @return oggetto con metriche dettagliate della conversione
     */
    public ConversionStatistics getStatistics() {
        return statistics;
    }

    /**
     * Restituisce mapping variabili per tracciabilità.
     *
     * @return mappa ID_numerico -> nome_simbolico
     */
    public Map<Integer, String> getVariableMapping() {
        return new HashMap<>(variableMapping);
    }

    /**
     * Reset per nuovo utilizzo del convertitore.
     */
    public void reset() {
        resetConversionState();
        LOGGER.fine("StandardConverterCNF resettato per nuovo utilizzo");
    }

    /**
     * Rappresentazione testuale del convertitore per debugging.
     */
    @Override
    public String toString() {
        return String.format("StandardConverterCNF[clauses=%d, variables=%d, lines_processed=%d]",
                statistics.extractedClauses, statistics.uniqueVariables, statistics.totalLines);
    }

    //endregion

    //region CLASSI DI SUPPORTO

    /**
     * STATISTICHE CONVERSIONE - Metriche dettagliate del processo di conversione
     *
     * Raccoglie informazioni quantitative sulla conversione per analisi
     * dell'efficacia del parsing e qualità del file input.
     */
    public static class ConversionStatistics {
        /** Numero totale di righe nel file */
        public int totalLines = 0;

        /** Numero di righe saltate (commenti, header, vuote) */
        public int skippedLines = 0;

        /** Numero di righe con clausole valide */
        public int validLines = 0;

        /** Numero di righe con formato non valido */
        public int invalidLines = 0;

        /** Numero di clausole estratte con successo */
        public int extractedClauses = 0;

        /** Numero di variabili uniche identificate */
        public int uniqueVariables = 0;

        /**
         * Calcola percentuale di successo del parsing.
         *
         * @return percentuale righe valide sul totale (0.0-100.0)
         */
        public double getSuccessRate() {
            return totalLines > 0 ? (double) validLines / totalLines * 100.0 : 0.0;
        }

        /**
         * Verifica se la conversione è stata successful.
         *
         * @return true se almeno una clausola è stata estratta
         */
        public boolean isSuccessful() {
            return extractedClauses > 0 && validLines > 0;
        }

        /**
         * Rappresentazione testuale delle statistiche.
         */
        @Override
        public String toString() {
            return String.format("ConversionStats[total=%d, valid=%d, clauses=%d, vars=%d, success=%.1f%%]",
                    totalLines, validLines, extractedClauses, uniqueVariables, getSuccessRate());
        }
    }

    //endregion
}