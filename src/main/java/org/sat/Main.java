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
import org.sat.optionalfeatures.SubsumptionPrinciple;
import org.sat.optionalfeatures.TseitinConverter;

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
 * - Principio di sussunzione per eliminazione clausole ridondanti
 *
 * @author Amos Lo Verde
 * @version 1.7.1
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
    private static final String OPT_PARAM = "-opt=";

    /**
     * Opzioni di ottimizzazione
     */
    private static final String OPT_SUBSUMPTION = "s";
    private static final String OPT_WATCHED_LITERALS = "w";
    private static final String OPT_RESTART = "r";
    private static final String OPT_TSEITIN = "t";
    private static final String OPT_ALL = "all";

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

        // Mostra ottimizzazioni attive
        List<String> activeOptimizations = new ArrayList<>();
        if (config.useSubsumption) activeOptimizations.add("Sussunzione");
        if (config.useWatchedLiterals) activeOptimizations.add("Watched Literals");
        if (config.useRestart) activeOptimizations.add("Restart");
        if (config.useTseitin) activeOptimizations.add("Tseitin");

        if (activeOptimizations.isEmpty()) {
            System.out.println("Ottimizzazioni: Nessuna");
        } else {
            System.out.println("Ottimizzazioni: " + String.join(", ", activeOptimizations));
        }

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
            processFile(config.inputPath, config.outputPath, config.timeoutSeconds, config);
        } else {
            LOGGER.info("Esecuzione modalità directory: " + config.inputPath);
            processDirectory(config.inputPath, config.outputPath, config.timeoutSeconds, config);
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
     * 5. [OPZIONALE] Applicazione principio di sussunzione se richiesto
     * 6. Risoluzione SAT con CDCL e timeout
     * 7. Salvataggio risultati e statistiche
     *
     * @param filePath percorso file da elaborare
     * @param outputPath directory output (null = default)
     * @param timeoutSeconds timeout per risoluzione SAT
     * @param config configurazione ottimizzazioni
     * @return risultato elaborazione
     */
    private static ProcessResult processFile(String filePath, String outputPath, int timeoutSeconds, Configuration config) {
        System.out.println("\n=== ELABORAZIONE FILE ===");
        System.out.println("File: " + Paths.get(filePath).getFileName());

        // Mostra ottimizzazioni attive
        List<String> activeOpts = new ArrayList<>();
        if (config.useTseitin) activeOpts.add("Tseitin");
        if (config.useSubsumption) activeOpts.add("Sussunzione");
        if (config.useWatchedLiterals) activeOpts.add("Watched Literals");
        if (config.useRestart) activeOpts.add("Restart");

        System.out.println("Ottimizzazioni: " + (activeOpts.isEmpty() ? "Nessuna" : String.join(", ", activeOpts)));
        System.out.println("========================\n");

        try {
            // STEP 1: Lettura formula logica
            String formulaText = readFormulaFromFile(filePath);

            // STEP 2: Conversione in CNF
            CNFConversionResult cnfResult = convertToCNF(formulaText);

            // STEP 3: Salvataggio CNF standard (sempre eseguito)
            saveCNFToFile(cnfResult.cnfString, filePath, outputPath);

            // STEP 4: Conversione Tseitin (se richiesta)
            CNFConverter formulaToOptimize;
            String conversionInfo = "";
            boolean isECNF = false;

            if (config.useTseitin) {
                TseitinConversionResult tseitinResult = convertToECNF(cnfResult);
                formulaToOptimize = tseitinResult.ecnfFormula;
                conversionInfo = tseitinResult.conversionInfo;
                isECNF = true;

                // Salvataggio E-CNF - SOLO FORMULA
                saveECNFToFile(tseitinResult.ecnfString, filePath, outputPath);

                // Salvataggio statistiche Tseitin - FILE SEPARATO
                saveTseitinStatsToFile(conversionInfo, filePath, outputPath);
            } else {
                formulaToOptimize = cnfResult.cnfFormula;
            }

            // STEP 5: Applicazione principio di sussunzione (se richiesto)
            CNFConverter formulaToSolve = formulaToOptimize;
            String subsumptionInfo = "";

            if (config.useSubsumption) {
                SubsumptionOptimizationResult subsumptionResult = applySubsumptionOptimization(formulaToOptimize, isECNF);
                formulaToSolve = subsumptionResult.optimizedFormula;
                subsumptionInfo = subsumptionResult.optimizationInfo;

                // Salvataggio statistiche sussunzione
                saveSubsumptionStatsToFile(subsumptionInfo, filePath, outputPath, isECNF);
            }

            // STEP 6: Risoluzione SAT con timeout
            SATResult satResult = solveSATWithTimeout(formulaToSolve, timeoutSeconds);

            if (satResult == null) {
                // Salva file opzioni attive anche per timeout
                saveActiveOptionsFile(config, filePath, outputPath);
                return handleTimeoutCase(filePath, outputPath, timeoutSeconds, config);
            }

            // STEP 7: Salvataggio risultati
            saveResultsToFile(satResult, formulaToSolve, filePath, outputPath, conversionInfo, config);

            // STEP 8: Salvataggio file opzioni attive (se necessario)
            saveActiveOptionsFile(config, filePath, outputPath);

            // STEP 9: Visualizzazione statistiche
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
     * Applica il principio di sussunzione per ottimizzare la formula
     */
    private static SubsumptionOptimizationResult applySubsumptionOptimization(CNFConverter formula, boolean isECNF) throws Exception {
        String stepNumber = isECNF ? "3b" : "3a";
        System.out.println(stepNumber + ". Applicazione principio di sussunzione...");

        SubsumptionPrinciple subsumptionOptimizer = new SubsumptionPrinciple();
        CNFConverter optimizedFormula = subsumptionOptimizer.applySubsumption(formula);
        String optimizationInfo = subsumptionOptimizer.getOptimizationInfo();

        LOGGER.info("Formula ottimizzata con sussunzione: " + optimizedFormula.toString());
        LOGGER.info("Clausole eliminate: " + subsumptionOptimizer.getEliminatedClausesCount());

        return new SubsumptionOptimizationResult(optimizedFormula, optimizationInfo);
    }

    /**
     * Risolve una formula CNF utilizzando l'algoritmo CDCL con gestione timeout.
     * Utilizza ExecutorService per controllo temporale e interruzione sicura.
     */
    private static SATResult solveSATWithTimeout(CNFConverter cnfFormula, int timeoutSeconds) {
        System.out.println("4. Risoluzione SAT con CDCL (timeout: " + timeoutSeconds + "s)...");

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
    private static void processDirectory(String dirPath, String outputPath, int timeoutSeconds, Configuration config) {
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
            BatchResult batchResult = processBatch(txtFiles, outputPath, timeoutSeconds, config);

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
    private static BatchResult processBatch(List<File> files, String outputPath, int timeoutSeconds, Configuration config) {
        BatchResult result = new BatchResult(files.size());

        System.out.println("Timeout per file: " + timeoutSeconds + " secondi");

        // Mostra ottimizzazioni
        List<String> activeOpts = new ArrayList<>();
        if (config.useTseitin) activeOpts.add("Tseitin");
        if (config.useSubsumption) activeOpts.add("Sussunzione");
        if (config.useWatchedLiterals) activeOpts.add("Watched Literals");
        if (config.useRestart) activeOpts.add("Restart");

        System.out.println("Ottimizzazioni: " + (activeOpts.isEmpty() ? "Nessuna" : String.join(", ", activeOpts)) + "\n");

        for (File file : files) {
            try {
                System.out.println("Elaborazione: " + file.getName());

                ProcessResult fileResult = processFile(file.getAbsolutePath(), outputPath, timeoutSeconds, config);

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

        Path tseitinStatsDir = getStatsDirectory(originalFilePath, outputPath).resolve("TSEITIN");
        Files.createDirectories(tseitinStatsDir);

        String baseFileName = getBaseFileName(originalFilePath);
        Path statsFilePath = tseitinStatsDir.resolve(baseFileName + ".stats");

        try (FileWriter writer = new FileWriter(statsFilePath.toFile())) {
            writer.write(conversionInfo);
        }

        LOGGER.info("Statistiche Tseitin salvate: " + statsFilePath);
    }

    /**
     * Salva le statistiche di ottimizzazione sussunzione in file separato
     */
    private static void saveSubsumptionStatsToFile(String optimizationInfo, String originalFilePath, String outputPath, boolean isECNF) throws IOException {
        String stepNumber = isECNF ? "3c" : "3b";
        System.out.println(stepNumber + ". Salvataggio statistiche sussunzione...");

        Path subsumptionStatsDir = getStatsDirectory(originalFilePath, outputPath).resolve("SUBSUMPTION");
        Files.createDirectories(subsumptionStatsDir);

        String baseFileName = getBaseFileName(originalFilePath);
        Path statsFilePath = subsumptionStatsDir.resolve(baseFileName + ".stats");

        try (FileWriter writer = new FileWriter(statsFilePath.toFile())) {
            writer.write(optimizationInfo);
        }

        LOGGER.info("Statistiche sussunzione salvate: " + statsFilePath);
    }

    /**
     * Salva file con opzioni attive nella directory STATS
     */
    private static void saveActiveOptionsFile(Configuration config, String originalFilePath, String outputPath) throws IOException {
        // Verifica se ci sono ottimizzazioni attive
        List<String> activeOptions = new ArrayList<>();
        if (config.useTseitin) activeOptions.add("TSEITIN");
        if (config.useSubsumption) activeOptions.add("SUBSUMPTION");
        if (config.useWatchedLiterals) activeOptions.add("WATCHED_LITERALS");
        if (config.useRestart) activeOptions.add("RESTART");

        // Salva solo se ci sono opzioni attive
        if (!activeOptions.isEmpty()) {
            Path statsDir = getStatsDirectory(originalFilePath, outputPath);
            Files.createDirectories(statsDir);

            Path optionsFilePath = statsDir.resolve("opzioni_attive.txt");

            try (FileWriter writer = new FileWriter(optionsFilePath.toFile())) {
                writer.write("------------------\n");
                writer.write("| OPZIONI ATTIVE |\n");
                writer.write("------------------\n\n");

                if (config.useTseitin) {
                    writer.write("- TSEITIN (flag <t>): Trasformazione in formula equisoddisfacibile E-CNF.\n");
                }
                if (config.useSubsumption) {
                    writer.write("- SUBSUMPTION (flag <s>): Eliminazione delle clausole che contengono clausole più piccole.\n");
                }
                if (config.useWatchedLiterals) {
                    writer.write("- WATCHED_LITERALS (flag <w>): Ottimizzazione unit propagation con letterali osservati.\n");
                }
                if (config.useRestart) {
                    writer.write("- RESTART (flag <r>): Tecniche di riavvio per evitare stalli durante la ricerca.\n");
                }
            }

            LOGGER.info("File opzioni attive salvato: " + optionsFilePath);
        }
    }

    /**
     * Salva i risultati SAT completi con formato strutturato
     */
    private static void saveResultsToFile(SATResult result, CNFConverter cnfFormula,
                                          String originalFilePath, String outputPath,
                                          String conversionInfo, Configuration config) throws IOException {
        System.out.println("5. Salvataggio risultati...");

        Path resultDir = getResultDirectory(originalFilePath, outputPath);
        Files.createDirectories(resultDir);

        String baseFileName = getBaseFileName(originalFilePath);
        Path resultFilePath = resultDir.resolve(baseFileName + ".result");

        try (FileWriter writer = new FileWriter(resultFilePath.toFile())) {
            writeCompleteResult(writer, result, originalFilePath, cnfFormula, conversionInfo, config);
        }

        LOGGER.info("Risultati salvati: " + resultFilePath);
    }

    /**
     * Scrive un report completo strutturato del risultato SAT
     */
    private static void writeCompleteResult(FileWriter writer, SATResult result,
                                            String originalFilePath, CNFConverter cnfFormula,
                                            String conversionInfo, Configuration config) throws IOException {
        // Header del report
        writer.write("-------------------\n");
        writer.write("| RISOLUZIONE SAT |\n");
        writer.write("-------------------\n");
        writer.write("-> File originale: " + Paths.get(originalFilePath).getFileName() + "\n");
        writer.write("-> File CNF: " + getBaseFileName(originalFilePath) + ".cnf\n");

        if (config.useTseitin) {
            writer.write("-> File E-CNF: " + getBaseFileName(originalFilePath) + ".ecnf\n");
            writer.write("\n");
            writer.write("È stato utilizzato il solutore SAT sulla formula presente in " + getBaseFileName(originalFilePath) + ".ecnf\n");
        } else {
            writer.write("\n");
            writer.write("È stato utilizzato il solutore SAT sulla formula presente in " + getBaseFileName(originalFilePath) + ".cnf\n");
        }

        writer.write("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n");

        // Contenuto principale
        if (result.isSatisfiable()) {
            writeSATResult(writer, result, config.useTseitin);
        } else {
            writeUNSATResult(writer, result, config.useTseitin);
        }

        // Statistiche finali
        writer.write("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n");
        SATStatistics stats = result.getStatistics();
        writer.write("Decisioni: " + stats.getDecisions() + "\n");
        writer.write("Conflitti: " + stats.getConflicts() + "\n");
        writer.write("Propagazioni: " + stats.getPropagations() + "\n");
        writer.write("Clausole apprese: " + stats.getLearnedClauses() + "\n");
        writer.write("Tempo risoluzione: " + stats.getExecutionTimeMs() + " ms\n");
    }

    /**
     * Scrive risultato SAT con modello delle variabili
     */
    private static void writeSATResult(FileWriter writer, SATResult result, boolean useTseitin) throws IOException {
        String formulaType = useTseitin ? "E-CNF" : "CNF";
        writer.write("La formula " + formulaType + " è SAT.\n");
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
    private static void writeUNSATResult(FileWriter writer, SATResult result, boolean useTseitin) throws IOException {
        String formulaType = useTseitin ? "E-CNF" : "CNF";
        writer.write("La formula " + formulaType + " è UNSAT.\n");
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
    private static ProcessResult handleTimeoutCase(String filePath, String outputPath, int timeoutSeconds, Configuration config) throws IOException {
        System.out.println("TIMEOUT: Superato il limite di " + timeoutSeconds + " secondi");

        // Salva report specifico per timeout
        saveTimeoutResult(filePath, outputPath, timeoutSeconds, config);

        return ProcessResult.timeout();
    }

    /**
     * Crea un report specifico per casi di timeout
     */
    private static void saveTimeoutResult(String filePath, String outputPath, int timeoutSeconds, Configuration config) throws IOException {
        Path resultDir = getResultDirectory(filePath, outputPath);
        Files.createDirectories(resultDir);

        String baseFileName = getBaseFileName(filePath);
        Path resultFilePath = resultDir.resolve(baseFileName + ".result");

        try (FileWriter writer = new FileWriter(resultFilePath.toFile())) {
            writer.write("-------------------\n");
            writer.write("| RISOLUZIONE SAT |\n");
            writer.write("-------------------\n");
            writer.write("-> File originale: " + Paths.get(filePath).getFileName() + "\n");
            writer.write("-> File CNF: " + baseFileName + ".cnf\n");

            if (config.useTseitin) {
                writer.write("-> File E-CNF: " + baseFileName + ".ecnf\n");
                writer.write("\n");
                writer.write("È stato utilizzato il solutore SAT sulla formula presente in " + baseFileName + ".ecnf\n");
            } else {
                writer.write("\n");
                writer.write("È stato utilizzato il solutore SAT sulla formula presente in " + baseFileName + ".cnf\n");
            }

            writer.write("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n");
            writer.write("La risoluzione ha superato il tempo limite di " + timeoutSeconds + " secondi.\n");
            writer.write("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n");
            writer.write("Decisioni effettuate: N/A\n");
            writer.write("Conflitti: N/A\n");
            writer.write("Propagazioni: N/A\n");
            writer.write("Clausole apprese: N/A\n");
            writer.write("Tempo risoluzione: TIMEOUT\n");
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
     * Ottiene la directory per file statistiche (creata dinamicamente)
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
        System.out.println("  -opt=<flags>    Attiva ottimizzazioni specifiche:");
        System.out.println("                  s = Principio di sussunzione");
        System.out.println("                  w = Watched literals (futuro)");
        System.out.println("                  r = Tecniche di restart (futuro)");
        System.out.println("                  t = Trasformazione di Tseitin");
        System.out.println("                  all = Tutte le ottimizzazioni");
        System.out.println("  -h              Mostra questa guida\n");

        System.out.println("ESEMPI:");
        System.out.println("  java -jar solutore_SAT.jar -f formula.txt");
        System.out.println("  java -jar solutore_SAT.jar -f formula.txt -opt=t");
        System.out.println("  java -jar solutore_SAT.jar -f formula.txt -opt=st");
        System.out.println("  java -jar solutore_SAT.jar -f formula.txt -opt=all");
        System.out.println("  java -jar solutore_SAT.jar -d ./formule/ -o ./risultati/ -t 30 -opt=s");
        System.out.println("  java -jar solutore_SAT.jar -d ./formule/ -opt=sr -t 60\n");

        System.out.println("NOTE:");
        System.out.println("  • Le opzioni -f e -d sono mutuamente esclusive");
        System.out.println("  • Il solver supporta formule con operatori: AND, OR, NOT, ->, <->");
        System.out.println("  • Output automatico: file .cnf e .result nelle directory CNF/ e RESULT/");
        System.out.println("  • Con ottimizzazioni attive:");
        System.out.println("    - File .ecnf nella directory E-CNF/ (con -opt=t)");
        System.out.println("    - Statistiche organizzate in STATS/TSEITIN/ e STATS/SUBSUMPTION/");
        System.out.println("    - File opzioni_attive.txt nella directory STATS/");
        System.out.println("  • Tseitin è raccomandato per formule complesse (>8 operatori)");
        System.out.println("  • Sussunzione elimina clausole ridondanti che sono sovrainsieme di altre\n");
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
        final boolean useSubsumption;
        final boolean useWatchedLiterals;
        final boolean useRestart;

        Configuration(String inputPath, String outputPath, boolean isFileMode, int timeoutSeconds,
                      boolean useTseitin, boolean useSubsumption, boolean useWatchedLiterals, boolean useRestart) {
            this.inputPath = inputPath;
            this.outputPath = outputPath;
            this.isFileMode = isFileMode;
            this.timeoutSeconds = timeoutSeconds;
            this.useTseitin = useTseitin;
            this.useSubsumption = useSubsumption;
            this.useWatchedLiterals = useWatchedLiterals;
            this.useRestart = useRestart;
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
            boolean useSubsumption = false;
            boolean useWatchedLiterals = false;
            boolean useRestart = false;
            int timeoutSeconds = DEFAULT_TIMEOUT_SECONDS;

            for (int i = 0; i < args.length; i++) {
                if (args[i].equals(HELP_PARAM)) {
                    printHelp();
                    return null;
                } else if (args[i].equals(FILE_PARAM)) {
                    if (isDirectoryMode) {
                        throw new IllegalArgumentException("Impossibile specificare sia -f che -d");
                    }
                    inputPath = getNextArgument(args, i++, "file");
                    validateFileExists(inputPath);
                    isFileMode = true;
                } else if (args[i].equals(DIR_PARAM)) {
                    if (isFileMode) {
                        throw new IllegalArgumentException("Impossibile specificare sia -f che -d");
                    }
                    inputPath = getNextArgument(args, i++, "directory");
                    validateDirectoryExists(inputPath);
                    isDirectoryMode = true;
                } else if (args[i].equals(OUTPUT_PARAM)) {
                    outputPath = getNextArgument(args, i++, "directory di output");
                    validateOrCreateOutputDirectory(outputPath);
                } else if (args[i].equals(TIMEOUT_PARAM)) {
                    timeoutSeconds = parseAndValidateTimeout(args, i++);
                } else if (args[i].startsWith(OPT_PARAM)) {
                    String optValue = args[i].substring(OPT_PARAM.length());
                    OptimizationFlags flags = parseOptimizationFlags(optValue);
                    useTseitin = flags.tseitin;
                    useSubsumption = flags.subsumption;
                    useWatchedLiterals = flags.watchedLiterals;
                    useRestart = flags.restart;
                } else {
                    throw new IllegalArgumentException("Parametro sconosciuto: " + args[i]);
                }
            }

            // Validazione finale
            if (inputPath == null) {
                throw new IllegalArgumentException("Specificare un file (-f) o directory (-d)");
            }

            return new Configuration(inputPath, outputPath, isFileMode, timeoutSeconds,
                    useTseitin, useSubsumption, useWatchedLiterals, useRestart);
        }

        /**
         * Parsa le flag di ottimizzazione
         */
        private OptimizationFlags parseOptimizationFlags(String flagsStr) {
            if (flagsStr == null || flagsStr.trim().isEmpty()) {
                throw new IllegalArgumentException("Valore -opt vuoto");
            }

            boolean tseitin = false;
            boolean subsumption = false;
            boolean watchedLiterals = false;
            boolean restart = false;

            if (flagsStr.equals(OPT_ALL)) {
                // Tutte le ottimizzazioni
                tseitin = true;
                subsumption = true;
                watchedLiterals = true;
                restart = true;
            } else {
                // Parsing singole flag
                for (char flag : flagsStr.toCharArray()) {
                    switch (String.valueOf(flag)) {
                        case OPT_TSEITIN -> tseitin = true;
                        case OPT_SUBSUMPTION -> subsumption = true;
                        case OPT_WATCHED_LITERALS -> watchedLiterals = true;
                        case OPT_RESTART -> restart = true;
                        default -> throw new IllegalArgumentException("Flag ottimizzazione non riconosciuta: " + flag);
                    }
                }
            }

            return new OptimizationFlags(tseitin, subsumption, watchedLiterals, restart);
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
     * Flag di ottimizzazione parsate
     */
    private static class OptimizationFlags {
        final boolean tseitin;
        final boolean subsumption;
        final boolean watchedLiterals;
        final boolean restart;

        OptimizationFlags(boolean tseitin, boolean subsumption, boolean watchedLiterals, boolean restart) {
            this.tseitin = tseitin;
            this.subsumption = subsumption;
            this.watchedLiterals = watchedLiterals;
            this.restart = restart;
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

    /**
     * Risultato ottimizzazione sussunzione
     */
    private static class SubsumptionOptimizationResult {
        final CNFConverter optimizedFormula;
        final String optimizationInfo;

        SubsumptionOptimizationResult(CNFConverter optimizedFormula, String optimizationInfo) {
            this.optimizedFormula = optimizedFormula;
            this.optimizationInfo = optimizationInfo;
        }
    }

    //endregion
}