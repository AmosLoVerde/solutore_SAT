package org.sat;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.sat.antlr.org.sat.parser.LogicFormulaLexer;
import org.sat.cdcl.CDCLSolver;
import org.sat.cdcl.SATResult;
import org.sat.cdcl.SATStatistics;
import org.sat.cnf.CNFConverter;
import org.sat.cnf.LogicFormulaParser;
import org.sat.optimization.TseitinConverter;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.*;
import java.util.logging.Logger;
import java.util.logging.Level;
import java.util.stream.Stream;

/**
 * SOLUTORE SAT CDCL - Punto di ingresso principale
 *
 * Questo solutore implementa l'algoritmo CDCL (Conflict-Driven Clause Learning) per risolvere
 * problemi di soddisfacibilità booleana (SAT).
 *
 * ALGORITMI IMPLEMENTATI:
 * - CDCL con euristica VSIDS per selezione variabili
 * - First 1UIP per apprendimento clausole e backjumping
 * - Generazione automatica di prove per formule UNSAT
 * - Unit propagation con rilevamento conflitti
 * - Trasformazione di Tseitin per E-CNF equisoddisfacibili
 *
 * @author Amos Lo Verde
 * @version 1.6.0
 */
public final class Main {

    //region CONFIGURAZIONE E COSTANTI

    private static final Logger LOGGER = Logger.getLogger(Main.class.getName());

    /**
     * Parametri linea di comando
     */
    private static final String HELP_PARAM = "-h";
    private static final String FILE_PARAM = "-f";
    private static final String DIR_PARAM = "-d";
    private static final String OUTPUT_PARAM = "-o";
    private static final String TIMEOUT_PARAM = "-t";
    private static final String CONVERT_PARAM = "-convert=tseitin";

    /**
     * Configurazioni timeout
     */
    private static final int DEFAULT_TIMEOUT_SECONDS = 10;
    private static final int MIN_TIMEOUT_SECONDS = 5;

    /**
     * Costruttore privato - classe utility non istanziabile
     */
    private Main() {
        throw new UnsupportedOperationException("Classe utility - non istanziabile");
    }

    //endregion


    //region PUNTO DI INGRESSO PRINCIPALE

    /**
     * Entry point dell'applicazione. Coordina l'intero flusso di elaborazione.
     *
     * FLUSSO:
     * 1. Parsing e validazione parametri linea di comando
     * 2. Selezione modalità operativa (file singolo vs directory)
     * 3. Esecuzione elaborazione con gestione errori
     *
     * @param args parametri linea di comando
     */
    public static void main(String[] args) {
        LOGGER.info("=== AVVIO SOLUTORE SAT CDCL ===");

        try {
            // Validazione input base
            if (args.length == 0) {
                System.out.println("Nessun parametro fornito. Usa -h per visualizzare l'help.");
                return;
            }

            // Parsing parametri con validazione
            Configuration config = parseAndValidateArguments(args);
            if (config == null) return; // Help mostrato o errore

            // Mostra configurazione per conferma utente
            displayConfiguration(config);

            // Esecuzione modalità appropriata
            executeSelectedMode(config);

        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Errore critico nell'applicazione", e);
            System.err.println("ERRORE CRITICO: " + e.getMessage());
            System.exit(1);
        } finally {
            LOGGER.info("=== FINE ESECUZIONE SOLUTORE SAT ===");
        }
    }

    //endregion


    //region PARSING E VALIDAZIONE PARAMETRI

    /**
     * Analizza e valida tutti i parametri della linea di comando.
     * Gestisce help, validazione input e creazione configurazione.
     */
    private static Configuration parseAndValidateArguments(String[] args) {
        try {
            CommandLineParser parser = new CommandLineParser();
            return parser.parse(args);
        } catch (IllegalArgumentException e) {
            LOGGER.warning("Errore nei parametri: " + e.getMessage());
            System.out.println("Errore: " + e.getMessage());
            return null;
        }
    }

    /**
     * Mostra la configurazione corrente per conferma utente
     */
    private static void displayConfiguration(Configuration config) {
        System.out.println("\n=== CONFIGURAZIONE SOLUTORE SAT ===");
        System.out.println("Timeout: " + config.timeoutSeconds + " secondi");
        System.out.println("Trasformazione: " + (config.useTseitin ? "Tseitin (E-CNF)" : "CNF standard"));

        if (config.isFileMode) {
            System.out.println("Modalità: File singolo");
            System.out.println("File input: " + config.inputPath);
        } else {
            System.out.println("Modalità: Directory");
            System.out.println("Directory input: " + config.inputPath);
        }

        String outputInfo = config.outputPath != null ? config.outputPath : "Default (stessa cartella input)";
        System.out.println("Directory output: " + outputInfo);
        System.out.println("====================================\n");
    }

    /**
     * Esegue la modalità operativa selezionata (file singolo o directory)
     */
    private static void executeSelectedMode(Configuration config) {
        if (config.isFileMode) {
            LOGGER.info("Esecuzione modalità file singolo: " + config.inputPath);
            processFile(config.inputPath, config.outputPath, config.timeoutSeconds, config.useTseitin);
        } else {
            LOGGER.info("Esecuzione modalità directory: " + config.inputPath);
            processDirectory(config.inputPath, config.outputPath, config.timeoutSeconds, config.useTseitin);
        }
    }

    //endregion


    //region ELABORAZIONE FILE SINGOLO

    /**
     * Elabora un singolo file contenente una formula logica.
     *
     * PIPELINE COMPLETA:
     * 1. Lettura formula da file
     * 2. Parsing con ANTLR (grammatica logica proposizionale)
     * 3. Conversione automatica in CNF
     * 4. [OPZIONALE] Conversione Tseitin in E-CNF se richiesta
     * 5. Risoluzione SAT con CDCL e timeout
     * 6. Salvataggio risultati e statistiche
     *
     * @param filePath percorso file da elaborare
     * @param outputPath directory output (null = default)
     * @param timeoutSeconds timeout per risoluzione SAT
     * @param useTseitin flag per conversione Tseitin
     * @return risultato elaborazione
     */
    private static ProcessResult processFile(String filePath, String outputPath, int timeoutSeconds, boolean useTseitin) {
        System.out.println("\n=== ELABORAZIONE FILE ===");
        System.out.println("File: " + Paths.get(filePath).getFileName());
        System.out.println("Conversione: " + (useTseitin ? "Tseitin (E-CNF)" : "CNF standard"));
        System.out.println("========================\n");

        try {
            // STEP 1: Lettura formula logica
            String formulaText = readFormulaFromFile(filePath);

            // STEP 2: Conversione in CNF
            CNFConversionResult cnfResult = convertToCNF(formulaText);

            // STEP 3: Salvataggio CNF standard (sempre eseguito)
            saveCNFToFile(cnfResult.cnfString, filePath, outputPath);

            // STEP 4: Conversione Tseitin (se richiesta)
            CNFConverter formulaToSolve;
            String conversionInfo = "";

            if (useTseitin) {
                TseitinConversionResult tseitinResult = convertToECNF(cnfResult);
                formulaToSolve = tseitinResult.ecnfFormula;
                conversionInfo = tseitinResult.conversionInfo;

                // Salvataggio E-CNF - SOLO FORMULA
                saveECNFToFile(tseitinResult.ecnfString, filePath, outputPath);

                // Salvataggio statistiche Tseitin - FILE SEPARATO
                saveTseitinStatsToFile(conversionInfo, filePath, outputPath);
            } else {
                formulaToSolve = cnfResult.cnfFormula;
            }

            // STEP 5: Risoluzione SAT con timeout
            SATResult satResult = solveSATWithTimeout(formulaToSolve, timeoutSeconds);

            if (satResult == null) {
                return handleTimeoutCase(filePath, outputPath, timeoutSeconds);
            }

            // STEP 6: Salvataggio risultati
            saveResultsToFile(satResult, formulaToSolve, filePath, outputPath, conversionInfo, useTseitin);

            // STEP 7: Visualizzazione statistiche
            displayFinalStatistics(satResult, formulaToSolve);

            return ProcessResult.success();

        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Errore elaborazione file: " + filePath, e);
            System.out.println("Errore durante l'elaborazione: " + e.getMessage());
            return ProcessResult.error();
        }
    }

    /**
     * Legge e normalizza il contenuto di una formula logica da file
     */
    private static String readFormulaFromFile(String filePath) throws IOException {
        System.out.println("1. Lettura formula logica...");

        String content = Files.readString(Path.of(filePath)).trim();
        LOGGER.info("Formula letta: " + content);

        return content;
    }

    /**
     * Converte una formula da notazione infix a forma normale congiuntiva (CNF).
     * Utilizza ANTLR per parsing e CNFConverter per trasformazione.
     */
    private static CNFConversionResult convertToCNF(String formulaText) throws Exception {
        System.out.println("2. Conversione in CNF...");

        // Setup pipeline ANTLR
        CharStream input = CharStreams.fromString(formulaText);
        LogicFormulaLexer lexer = new LogicFormulaLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        org.sat.antlr.org.sat.parser.LogicFormulaParser parser =
                new org.sat.antlr.org.sat.parser.LogicFormulaParser(tokens);

        // Parsing e conversione
        ParseTree tree = parser.formula();
        LogicFormulaParser converter = new LogicFormulaParser();
        CNFConverter formula = converter.visit(tree);
        CNFConverter cnfFormula = formula.toCNF();
        String cnfString = cnfFormula.toString();

        LOGGER.info("Formula CNF generata: " + cnfString);
        return new CNFConversionResult(cnfFormula, cnfString);
    }

    /**
     * Converte una formula CNF in E-CNF utilizzando l'algoritmo di Tseitin.
     */
    private static TseitinConversionResult convertToECNF(CNFConversionResult cnfResult) throws Exception {
        System.out.println("3a. Conversione Tseitin in E-CNF...");

        TseitinConverter tseitinConverter = new TseitinConverter();
        CNFConverter ecnfFormula = tseitinConverter.convertToECNF(cnfResult.cnfFormula);
        String ecnfString = ecnfFormula.toString();
        String conversionInfo = tseitinConverter.getConversionInfo();

        LOGGER.info("Formula E-CNF generata: " + ecnfString);
        return new TseitinConversionResult(ecnfFormula, ecnfString, conversionInfo);
    }

    /**
     * Risolve una formula CNF utilizzando l'algoritmo CDCL con gestione timeout.
     * Utilizza ExecutorService per controllo temporale e interruzione sicura.
     */
    private static SATResult solveSATWithTimeout(CNFConverter cnfFormula, int timeoutSeconds) {
        String stepNumber = "4";
        System.out.println(stepNumber + ". Risoluzione SAT con CDCL (timeout: " + timeoutSeconds + "s)...");

        ExecutorService executor = Executors.newSingleThreadExecutor();
        CDCLSolver solver = new CDCLSolver(cnfFormula);

        try {
            // Esecuzione asincrona con timeout
            Callable<SATResult> solverTask = solver::solve;
            Future<SATResult> future = executor.submit(solverTask);

            return future.get(timeoutSeconds, TimeUnit.SECONDS);

        } catch (TimeoutException e) {
            LOGGER.warning("Timeout raggiunto dopo " + timeoutSeconds + " secondi");
            return null; // Indica timeout al chiamante

        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Errore durante risoluzione SAT", e);
            throw new RuntimeException("Errore nella risoluzione SAT", e);

        } finally {
            executor.shutdownNow(); // Terminazione forzata
        }
    }

    //endregion


    // region ELABORAZIONE DIRECTORY

    /**
     * Elabora tutti i file .txt in una directory specificata.
     * Fornisce elaborazione batch con statistiche aggregate.
     */
    private static void processDirectory(String dirPath, String outputPath, int timeoutSeconds, boolean useTseitin) {
        LOGGER.info("Inizio elaborazione directory: " + dirPath);

        // Validazione directory input
        if (!validateInputDirectory(dirPath)) return;

        try {
            // Raccolta file da elaborare
            List<File> txtFiles = collectTxtFiles(dirPath);
            if (txtFiles.isEmpty()) {
                System.out.println("Nessun file .txt trovato nella directory specificata.");
                return;
            }

            // Elaborazione sequenziale batch
            BatchResult batchResult = processBatch(txtFiles, outputPath, timeoutSeconds, useTseitin);

            // Riepilogo finale
            displayBatchSummary(batchResult);

        } catch (IOException e) {
            LOGGER.log(Level.SEVERE, "Errore accesso directory", e);
            System.out.println("Errore durante l'accesso alla directory: " + e.getMessage());
        }
    }

    /**
     * Raccoglie tutti i file .txt dalla directory, ordinati alfabeticamente
     */
    private static List<File> collectTxtFiles(String dirPath) throws IOException {
        System.out.println("Ricerca file .txt nella directory...");

        List<File> txtFiles;
        try (Stream<Path> pathStream = Files.list(Paths.get(dirPath))) {
            txtFiles = pathStream
                    .filter(path -> path.toString().toLowerCase().endsWith(".txt"))
                    .map(Path::toFile)
                    .sorted(Comparator.comparing(File::getName))
                    .toList();
        }

        System.out.println("Trovati " + txtFiles.size() + " file .txt da elaborare.");
        return txtFiles;
    }

    /**
     * Elabora sequenzialmente una lista di file con gestione errori isolata
     */
    private static BatchResult processBatch(List<File> files, String outputPath, int timeoutSeconds, boolean useTseitin) {
        BatchResult result = new BatchResult(files.size());

        System.out.println("Timeout per file: " + timeoutSeconds + " secondi");
        System.out.println("Conversione: " + (useTseitin ? "Tseitin (E-CNF)" : "CNF standard") + "\n");

        for (File file : files) {
            try {
                System.out.println("Elaborazione: " + file.getName());

                ProcessResult fileResult = processFile(file.getAbsolutePath(), outputPath, timeoutSeconds, useTseitin);

                // Aggiornamento statistiche batch
                if (fileResult.isSuccess()) {
                    result.incrementSuccess();
                } else if (fileResult.isTimeout()) {
                    result.incrementTimeout();
                } else {
                    result.incrementError();
                }

            } catch (Exception e) {
                LOGGER.log(Level.WARNING, "Errore file: " + file.getName(), e);
                System.out.println("Errore: " + e.getMessage());
                result.incrementError();
            }

            System.out.println(); // Separatore visivo
        }

        return result;
    }

    //endregion


    // region SALVATAGGIO E OUTPUT

    /**
     * Salva la formula CNF in un file dedicato per tracciabilità
     */
    private static void saveCNFToFile(String cnfString, String originalFilePath, String outputPath) throws IOException {
        System.out.println("3. Salvataggio formula CNF...");

        Path cnfDir = getCNFDirectory(originalFilePath, outputPath);
        Files.createDirectories(cnfDir);

        String baseFileName = getBaseFileName(originalFilePath);
        Path cnfFilePath = cnfDir.resolve(baseFileName + ".cnf");

        try (FileWriter writer = new FileWriter(cnfFilePath.toFile())) {
            writer.write(cnfString);
        }

        LOGGER.info("Formula CNF salvata: " + cnfFilePath);
    }

    /**
     * Salva la formula E-CNF (Tseitin) in un file dedicato - SOLO FORMULA
     */
    private static void saveECNFToFile(String ecnfString, String originalFilePath, String outputPath) throws IOException {
        System.out.println("3b. Salvataggio formula E-CNF...");

        Path ecnfDir = getECNFDirectory(originalFilePath, outputPath);
        Files.createDirectories(ecnfDir);

        String baseFileName = getBaseFileName(originalFilePath);
        Path ecnfFilePath = ecnfDir.resolve(baseFileName + ".ecnf");

        // SOLO LA FORMULA CONVERTITA - nessun commento o metadata
        try (FileWriter writer = new FileWriter(ecnfFilePath.toFile())) {
            writer.write(ecnfString);
        }

        LOGGER.info("Formula E-CNF salvata: " + ecnfFilePath);
    }

    /**
     * Salva le statistiche di conversione Tseitin in file separato
     */
    private static void saveTseitinStatsToFile(String conversionInfo, String originalFilePath, String outputPath) throws IOException {
        System.out.println("3c. Salvataggio statistiche conversione Tseitin...");

        Path statsDir = getStatsDirectory(originalFilePath, outputPath);
        Files.createDirectories(statsDir);

        String baseFileName = getBaseFileName(originalFilePath);
        Path statsFilePath = statsDir.resolve(baseFileName + ".stats");

        try (FileWriter writer = new FileWriter(statsFilePath.toFile())) {
            writer.write(conversionInfo);
        }

        LOGGER.info("Statistiche Tseitin salvate: " + statsFilePath);
    }

    /**
     * Salva i risultati SAT completi con formato strutturato
     */
    private static void saveResultsToFile(SATResult result, CNFConverter cnfFormula,
                                          String originalFilePath, String outputPath,
                                          String conversionInfo, boolean useTseitin) throws IOException {
        String stepNumber = useTseitin ? "5" : "5";
        System.out.println(stepNumber + ". Salvataggio risultati...");

        Path resultDir = getResultDirectory(originalFilePath, outputPath);
        Files.createDirectories(resultDir);

        String baseFileName = getBaseFileName(originalFilePath);
        Path resultFilePath = resultDir.resolve(baseFileName + ".result");

        try (FileWriter writer = new FileWriter(resultFilePath.toFile())) {
            writeCompleteResult(writer, result, originalFilePath, cnfFormula, conversionInfo, useTseitin);
        }

        LOGGER.info("Risultati salvati: " + resultFilePath);
    }

    /**
     * Scrive un report completo strutturato del risultato SAT
     */
    private static void writeCompleteResult(FileWriter writer, SATResult result,
                                            String originalFilePath, CNFConverter cnfFormula,
                                            String conversionInfo, boolean useTseitin) throws IOException {
        // Header del report
        writer.write("-------------------\n");
        writer.write("| RISOLUZIONE SAT |\n");
        writer.write("-------------------\n");
        writer.write("-> File originale: " + Paths.get(originalFilePath).getFileName() + "\n");
        writer.write("-> File CNF: " + getBaseFileName(originalFilePath) + ".cnf\n");

        if (useTseitin) {
            writer.write("-> File E-CNF: " + getBaseFileName(originalFilePath) + ".ecnf\n");
            writer.write("-> File statistiche: " + getBaseFileName(originalFilePath) + ".stats\n");
            writer.write("-> Trasformazione: Tseitin (E-CNF)\n");
        } else {
            writer.write("-> Trasformazione: CNF standard\n");
        }

        writer.write("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n");

        // Contenuto principale
        if (result.isSatisfiable()) {
            writeSATResult(writer, result);
        } else {
            writeUNSATResult(writer, result);
        }

        // Statistiche finali
        writer.write("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n");
        SATStatistics stats = result.getStatistics();
        writer.write("Decisioni: " + stats.getDecisions() + "\n");
        writer.write("Conflitti: " + stats.getConflicts() + "\n");
        writer.write("Tempo risoluzione: " + stats.getExecutionTimeMs() + " ms\n");
    }

    /**
     * Scrive risultato SAT con modello delle variabili
     */
    private static void writeSATResult(FileWriter writer, SATResult result) throws IOException {
        writer.write("La formula CNF è SAT.\n");
        writer.write("Modello = {");

        if (result.getAssignment() != null && !result.getAssignment().isEmpty()) {
            String modelString = result.getAssignment().entrySet().stream()
                    .sorted(Map.Entry.comparingByKey())
                    .map(entry -> entry.getKey() + " = " + (entry.getValue() ? "true" : "false"))
                    .reduce((a, b) -> a + ", " + b)
                    .orElse("");
            writer.write(modelString);
        } else {
            writer.write("nessun modello disponibile");
        }

        writer.write("}\n");
    }

    /**
     * Scrive risultato UNSAT con prova di risoluzione
     */
    private static void writeUNSATResult(FileWriter writer, SATResult result) throws IOException {
        writer.write("La formula CNF è UNSAT.\n");
        writer.write("Prova generata:\n");

        if (result.getProof() != null && !result.getProof().trim().isEmpty()) {
            // Pulizia prova da numerazione automatica
            String cleanedProof = result.getProof().replaceAll("(?m)^\\s*\\d+\\.\\s*", "");
            writer.write(cleanedProof);

            // Verifica presenza clausola vuota
            if (!result.getProof().toLowerCase().contains("[]")) {
                writer.write("\n\nLa clausola vuota [] è stata derivata dalla sequenza di risoluzione.");
            }
        } else {
            writer.write("ERRORE: Nessuna prova disponibile per formula UNSAT.\n");
            LOGGER.severe("Formula UNSAT senza prova - possibile bug");
        }
    }

    //endregion


    //region GESTIONE TIMEOUT E CASI SPECIALI

    /**
     * Gestisce il caso di timeout durante risoluzione SAT
     */
    private static ProcessResult handleTimeoutCase(String filePath, String outputPath, int timeoutSeconds) throws IOException {
        System.out.println("TIMEOUT: Superato il limite di " + timeoutSeconds + " secondi");

        // Salva report specifico per timeout
        saveTimeoutResult(filePath, outputPath, timeoutSeconds);

        return ProcessResult.timeout();
    }

    /**
     * Crea un report specifico per casi di timeout
     */
    private static void saveTimeoutResult(String filePath, String outputPath, int timeoutSeconds) throws IOException {
        Path resultDir = getResultDirectory(filePath, outputPath);
        Files.createDirectories(resultDir);

        String baseFileName = getBaseFileName(filePath);
        Path resultFilePath = resultDir.resolve(baseFileName + ".result");

        try (FileWriter writer = new FileWriter(resultFilePath.toFile())) {
            writer.write("-------------------\n");
            writer.write("| RISOLUZIONE SAT |\n");
            writer.write("-------------------\n");
            writer.write("-> File originale: " + Paths.get(filePath).getFileName() + "\n");
            writer.write("-> File CNF: " + baseFileName + ".cnf\n\n");
            writer.write("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n");
            writer.write("La risoluzione ha superato il tempo limite di " + timeoutSeconds + " secondi.\n");
            writer.write("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n");
            writer.write("Decisioni effettuate: N/A\n");
            writer.write("Conflitti: N/A\n");
        }
    }

    //endregion


    //region VISUALIZZAZIONE STATISTICHE

    /**
     * Visualizza statistiche finali dettagliate per singolo file
     */
    private static void displayFinalStatistics(SATResult result, CNFConverter cnfFormula) {
        System.out.println("6. Elaborazione completata!\n");

        String resultStr = result.isSatisfiable() ? "SAT" : "UNSAT";
        int variableCount = extractVariableCount(cnfFormula);
        int clauseCount = extractClauseCount(cnfFormula);

        result.getStatistics().printDetailedStats(variableCount, clauseCount, resultStr);
    }

    /**
     * Mostra riepilogo completo per elaborazione batch
     */
    private static void displayBatchSummary(BatchResult result) {
        System.out.println("\n=== RIEPILOGO ELABORAZIONE DIRECTORY ===");
        System.out.println("File .txt trovati: " + result.totalFiles);
        System.out.println("File elaborati con successo: " + result.successCount);
        System.out.println("File con timeout: " + result.timeoutCount);
        System.out.println("File con errori: " + result.errorCount);

        if (result.totalFiles > 0) {
            double successRate = (double) result.successCount / result.totalFiles * 100;
            System.out.printf("Tasso di successo: %.1f%%\n", successRate);
        }

        System.out.println("=========================================\n");
    }

    //endregion


    //region UTILITÀ E HELPER METHODS

    /**
     * Ottiene la directory per file CNF (creata dinamicamente)
     */
    private static Path getCNFDirectory(String originalFilePath, String outputPath) {
        if (outputPath != null) {
            return Paths.get(outputPath).resolve("CNF");
        } else {
            Path parentDir = Paths.get(originalFilePath).getParent();
            return parentDir != null ? parentDir.resolve("CNF") : Paths.get("CNF");
        }
    }

    /**
     * Ottiene la directory per file E-CNF (creata dinamicamente)
     */
    private static Path getECNFDirectory(String originalFilePath, String outputPath) {
        if (outputPath != null) {
            return Paths.get(outputPath).resolve("E-CNF");
        } else {
            Path parentDir = Paths.get(originalFilePath).getParent();
            return parentDir != null ? parentDir.resolve("E-CNF") : Paths.get("E-CNF");
        }
    }

    /**
     * Ottiene la directory per file statistiche Tseitin (creata dinamicamente)
     */
    private static Path getStatsDirectory(String originalFilePath, String outputPath) {
        if (outputPath != null) {
            return Paths.get(outputPath).resolve("STATS");
        } else {
            Path parentDir = Paths.get(originalFilePath).getParent();
            return parentDir != null ? parentDir.resolve("STATS") : Paths.get("STATS");
        }
    }

    /**
     * Ottiene la directory per file risultati (creata dinamicamente)
     */
    private static Path getResultDirectory(String originalFilePath, String outputPath) {
        if (outputPath != null) {
            return Paths.get(outputPath).resolve("RESULT");
        } else {
            Path parentDir = Paths.get(originalFilePath).getParent();
            return parentDir != null ? parentDir.resolve("RESULT") : Paths.get("RESULT");
        }
    }

    /**
     * Estrae nome base del file senza estensione
     */
    private static String getBaseFileName(String filePath) {
        String fileName = Paths.get(filePath).getFileName().toString();
        return fileName.substring(0, fileName.lastIndexOf('.'));
    }

    /**
     * Valida directory di input per accessibilità
     */
    private static boolean validateInputDirectory(String dirPath) {
        File dir = new File(dirPath);

        if (!dir.exists() || !dir.isDirectory()) {
            System.out.println("Errore: directory non esistente o non valida: " + dirPath);
            return false;
        }

        if (!dir.canRead()) {
            System.out.println("Errore: directory non leggibile: " + dirPath);
            return false;
        }

        return true;
    }

    /**
     * Estrae numero di variabili uniche dalla formula CNF
     */
    private static int extractVariableCount(CNFConverter cnfFormula) {
        Set<String> variables = new HashSet<>();
        collectVariablesRecursively(cnfFormula, variables);
        return variables.size();
    }

    /**
     * Raccoglie ricorsivamente tutte le variabili dalla formula
     */
    private static void collectVariablesRecursively(CNFConverter formula, Set<String> variables) {
        if (formula == null) return;

        switch (formula.type) {
            case ATOM -> variables.add(formula.atom);
            case NOT -> {
                if (formula.operand != null && formula.operand.type == CNFConverter.Type.ATOM) {
                    variables.add(formula.operand.atom);
                } else if (formula.operand != null) {
                    collectVariablesRecursively(formula.operand, variables);
                }
            }
            case AND, OR -> {
                if (formula.operands != null) {
                    for (CNFConverter operand : formula.operands) {
                        collectVariablesRecursively(operand, variables);
                    }
                }
            }
            default -> {
                if (formula.operand != null) {
                    collectVariablesRecursively(formula.operand, variables);
                }
            }
        }
    }

    /**
     * Estrae numero di clausole dalla formula CNF
     */
    private static int extractClauseCount(CNFConverter cnfFormula) {
        if (cnfFormula == null) return 0;

        return switch (cnfFormula.type) {
            case AND -> cnfFormula.operands != null ? cnfFormula.operands.size() : 0;
            case OR, ATOM -> 1;
            case NOT -> {
                if (cnfFormula.operand != null && cnfFormula.operand.type == CNFConverter.Type.ATOM) {
                    yield 1;
                }
                yield extractClauseCount(cnfFormula.operand);
            }
            default -> 1;
        };
    }

    /**
     * Visualizza informazioni di help complete
     */
    private static void printHelp() {
        System.out.println("\n=== SOLUTORE SAT CDCL v2.1.0 ===");
        System.out.println("Solutore per problemi di soddisfacibilità booleana (SAT)");
        System.out.println("con algoritmo CDCL (Conflict-Driven Clause Learning)\n");

        System.out.println("UTILIZZO:");
        System.out.println("  java -jar solutore_SAT.jar [opzioni]\n");

        System.out.println("OPZIONI:");
        System.out.println("  -f <file>       Elabora un singolo file .txt");
        System.out.println("  -d <directory>  Elabora tutti i file .txt in una directory");
        System.out.println("  -o <directory>  Directory di output personalizzata (opzionale)");
        System.out.println("  -t <secondi>    Timeout per ogni formula (min: " + MIN_TIMEOUT_SECONDS +
                ", default: " + DEFAULT_TIMEOUT_SECONDS + ")");
        System.out.println("  -convert=tseitin Usa trasformazione di Tseitin per E-CNF (opzionale)");
        System.out.println("  -h              Mostra questa guida\n");

        System.out.println("ESEMPI:");
        System.out.println("  java -jar solutore_SAT.jar -f formula.txt");
        System.out.println("  java -jar solutore_SAT.jar -f formula.txt -convert=tseitin");
        System.out.println("  java -jar solutore_SAT.jar -d ./formule/ -o ./risultati/ -t 30");
        System.out.println("  java -jar solutore_SAT.jar -d ./formule/ -convert=tseitin -t 60\n");

        System.out.println("NOTE:");
        System.out.println("  • Le opzioni -f e -d sono mutuamente esclusive");
        System.out.println("  • Il solver supporta formule con operatori: AND, OR, NOT, ->, <->");
        System.out.println("  • Output automatico: file .cnf e .result nelle directory CNF/ e RESULT/");
        System.out.println("  • Con -convert=tseitin: file .ecnf e .stats nelle directory E-CNF/ e STATS/");
        System.out.println("  • Tseitin è raccomandato per formule complesse (>8 operatori)\n");
        System.out.println("=====================================\n");
    }

    //endregion


    //region CLASSI DI SUPPORTO E CONFIGURAZIONE

    /**
     * Configurazione validata dai parametri linea di comando
     */
    private static class Configuration {
        final String inputPath;
        final String outputPath;
        final boolean isFileMode;
        final int timeoutSeconds;
        final boolean useTseitin;

        Configuration(String inputPath, String outputPath, boolean isFileMode, int timeoutSeconds, boolean useTseitin) {
            this.inputPath = inputPath;
            this.outputPath = outputPath;
            this.isFileMode = isFileMode;
            this.timeoutSeconds = timeoutSeconds;
            this.useTseitin = useTseitin;
        }
    }

    /**
     * Parser per parametri linea di comando con validazione completa
     */
    private static class CommandLineParser {

        /**
         * Analizza e valida tutti i parametri forniti
         */
        public Configuration parse(String[] args) {
            String inputPath = null;
            String outputPath = null;
            boolean isFileMode = false;
            boolean isDirectoryMode = false;
            boolean useTseitin = false;
            int timeoutSeconds = DEFAULT_TIMEOUT_SECONDS;

            for (int i = 0; i < args.length; i++) {
                switch (args[i]) {
                    case HELP_PARAM -> {
                        printHelp();
                        return null;
                    }
                    case FILE_PARAM -> {
                        if (isDirectoryMode) {
                            throw new IllegalArgumentException("Impossibile specificare sia -f che -d");
                        }
                        inputPath = getNextArgument(args, i++, "file");
                        validateFileExists(inputPath);
                        isFileMode = true;
                    }
                    case DIR_PARAM -> {
                        if (isFileMode) {
                            throw new IllegalArgumentException("Impossibile specificare sia -f che -d");
                        }
                        inputPath = getNextArgument(args, i++, "directory");
                        validateDirectoryExists(inputPath);
                        isDirectoryMode = true;
                    }
                    case OUTPUT_PARAM -> {
                        outputPath = getNextArgument(args, i++, "directory di output");
                        validateOrCreateOutputDirectory(outputPath);
                    }
                    case TIMEOUT_PARAM -> {
                        timeoutSeconds = parseAndValidateTimeout(args, i++);
                    }
                    case CONVERT_PARAM -> {
                        useTseitin = true;
                    }
                    default -> throw new IllegalArgumentException("Parametro sconosciuto: " + args[i]);
                }
            }

            // Validazione finale
            if (inputPath == null) {
                throw new IllegalArgumentException("Specificare un file (-f) o directory (-d)");
            }

            return new Configuration(inputPath, outputPath, isFileMode, timeoutSeconds, useTseitin);
        }

        /**
         * Estrae il prossimo argomento con validazione presenza
         */
        private String getNextArgument(String[] args, int currentIndex, String argumentType) {
            if (currentIndex + 1 >= args.length) {
                throw new IllegalArgumentException("Parametro " + args[currentIndex] +
                        " richiede " + argumentType);
            }
            return args[currentIndex + 1];
        }

        /**
         * Valida e converte timeout con controlli range
         */
        private int parseAndValidateTimeout(String[] args, int currentIndex) {
            String timeoutStr = getNextArgument(args, currentIndex, "numero di secondi");

            try {
                int timeout = Integer.parseInt(timeoutStr);
                if (timeout < MIN_TIMEOUT_SECONDS) {
                    throw new IllegalArgumentException("Timeout minimo: " + MIN_TIMEOUT_SECONDS + " secondi");
                }
                return timeout;
            } catch (NumberFormatException e) {
                throw new IllegalArgumentException("Valore timeout non valido: " + timeoutStr);
            }
        }

        /**
         * Valida esistenza e accessibilità file
         */
        private void validateFileExists(String filePath) {
            File file = new File(filePath);
            if (!file.exists()) {
                throw new IllegalArgumentException("File non esistente: " + filePath);
            }
            if (!file.isFile()) {
                throw new IllegalArgumentException("Non è un file: " + filePath);
            }
            if (!file.canRead()) {
                throw new IllegalArgumentException("File non leggibile: " + filePath);
            }
        }

        /**
         * Valida esistenza e accessibilità directory
         */
        private void validateDirectoryExists(String dirPath) {
            File dir = new File(dirPath);
            if (!dir.exists()) {
                throw new IllegalArgumentException("Directory non esistente: " + dirPath);
            }
            if (!dir.isDirectory()) {
                throw new IllegalArgumentException("Non è una directory: " + dirPath);
            }
            if (!dir.canRead()) {
                throw new IllegalArgumentException("Directory non leggibile: " + dirPath);
            }
        }

        /**
         * Valida o crea directory di output con permessi
         */
        private void validateOrCreateOutputDirectory(String dirPath) {
            File dir = new File(dirPath);

            if (!dir.exists()) {
                System.out.println("Creazione directory di output: " + dirPath);
                if (!dir.mkdirs()) {
                    throw new IllegalArgumentException("Impossibile creare directory: " + dirPath);
                }
            } else if (!dir.isDirectory()) {
                throw new IllegalArgumentException("Il percorso non è una directory: " + dirPath);
            }

            if (!dir.canWrite()) {
                throw new IllegalArgumentException("Directory non scrivibile: " + dirPath);
            }
        }
    }

    /**
     * Risultato elaborazione singolo file
     */
    private static class ProcessResult {
        private final ResultType type;

        private enum ResultType { SUCCESS, TIMEOUT, ERROR }

        private ProcessResult(ResultType type) {
            this.type = type;
        }

        public boolean isSuccess() { return type == ResultType.SUCCESS; }
        public boolean isTimeout() { return type == ResultType.TIMEOUT; }
        public boolean isError() { return type == ResultType.ERROR; }

        public static ProcessResult success() { return new ProcessResult(ResultType.SUCCESS); }
        public static ProcessResult timeout() { return new ProcessResult(ResultType.TIMEOUT); }
        public static ProcessResult error() { return new ProcessResult(ResultType.ERROR); }
    }

    /**
     * Risultato elaborazione batch con statistiche aggregate
     */
    private static class BatchResult {
        final int totalFiles;
        int successCount = 0;
        int timeoutCount = 0;
        int errorCount = 0;

        BatchResult(int totalFiles) {
            this.totalFiles = totalFiles;
        }

        void incrementSuccess() { successCount++; }
        void incrementTimeout() { timeoutCount++; }
        void incrementError() { errorCount++; }
    }

    /**
     * Risultato conversione CNF con doppia rappresentazione
     */
    private static class CNFConversionResult {
        final CNFConverter cnfFormula;
        final String cnfString;

        CNFConversionResult(CNFConverter cnfFormula, String cnfString) {
            this.cnfFormula = cnfFormula;
            this.cnfString = cnfString;
        }
    }

    /**
     * Risultato conversione Tseitin con informazioni aggiuntive
     */
    private static class TseitinConversionResult {
        final CNFConverter ecnfFormula;
        final String ecnfString;
        final String conversionInfo;

        TseitinConversionResult(CNFConverter ecnfFormula, String ecnfString, String conversionInfo) {
            this.ecnfFormula = ecnfFormula;
            this.ecnfString = ecnfString;
            this.conversionInfo = conversionInfo;
        }
    }

    //endregion
}