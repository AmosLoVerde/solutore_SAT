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
 * SOLUTORE SAT CDCL
 *
 * Questo solutore implementa l'algoritmo CDCL (Conflict-Driven Clause Learning) per risolvere
 * problemi di soddisfacibilità booleana (SAT).
 *
 * ALGORITMI IMPLEMENTATI:
 * - CDCL con euristica VSIDS per la selezione di variabili
 * - First 1UIP per apprendimento clausole e backjumping
 * - Generazione automatica di prove per formule UNSAT
 * - Unit propagation con rilevamento conflitti
 * - Trasformazione di Tseitin per E-CNF equisoddisfacibili
 * - Principio di sussunzione per eliminazione clausole ridondanti
 * - Tecnica restart per prevenzione stalli (NUOVO)
 *
 * @author Amos Lo Verde
 * @version 1.8.3
 */
public final class Main {

    private static final Logger LOGGER = Logger.getLogger(Main.class.getName());

    //region CONFIGURAZIONE E COSTANTI

    // Parametri linea di comando
    private static final String HELP_PARAM = "-h";
    private static final String FILE_PARAM = "-f";
    private static final String DIR_PARAM = "-d";
    private static final String OUTPUT_PARAM = "-o";
    private static final String TIMEOUT_PARAM = "-t";
    private static final String OPT_PARAM = "-opt=";

    // Opzioni di ottimizzazione
    private static final String OPT_SUBSUMPTION = "s";
    private static final String OPT_WATCHED_LITERALS = "w";
    private static final String OPT_RESTART = "r";
    private static final String OPT_TSEITIN = "t";
    private static final String OPT_ALL = "all";

    // Configurazioni timeout
    private static final int DEFAULT_TIMEOUT_SECONDS = 10;
    private static final int MIN_TIMEOUT_SECONDS = 5;

    /** Costruttore privato - classe utility non istanziabile */
    private Main() {
        throw new UnsupportedOperationException("Classe utility - non istanziabile");
    }

    //endregion

    //region PUNTO DI INGRESSO E COORDINAMENTO PRINCIPALE

    /**
     * Entry point dell'applicazione. Coordina il flusso completo di elaborazione SAT.
     *
     * FLUSSO PRINCIPALE:
     * 1. Parsing e validazione parametri comando
     * 2. Configurazione ambiente di esecuzione
     * 3. Dispatch alla modalità appropriata (file/directory)
     * 4. Gestione errori e cleanup finale
     *
     * @param args parametri linea di comando
     */
    public static void main(String[] args) {
        LOGGER.info("=== AVVIO SOLUTORE SAT CDCL ===");

        try {
            // Validazione e parsing parametri
            if (args.length == 0) {
                System.out.println("Nessun parametro fornito. Usa -h per visualizzare l'help.");
                return;
            }

            Configuration config = parseCommandLineArguments(args);
            if (config == null) return; // Help mostrato o errore

            // Esecuzione modalità selezionata
            displayConfiguration(config);
            dispatchToExecutionMode(config);

        } catch (Exception e) {
            handleCriticalError(e);
        } finally {
            LOGGER.info("=== FINE ESECUZIONE SOLUTORE SAT ===");
        }
    }

    /**
     * Coordina il dispatch verso la modalità di esecuzione appropriata.
     * Seleziona tra elaborazione file singolo o batch directory.
     */
    private static void dispatchToExecutionMode(Configuration config) {
        if (config.isFileMode) {
            LOGGER.info("Modalità file singolo: " + config.inputPath);
            processSingleFile(config);
        } else {
            LOGGER.info("Modalità directory batch: " + config.inputPath);
            processDirectoryBatch(config);
        }
    }

    /**
     * Gestisce errori critici dell'applicazione con logging appropriato.
     */
    private static void handleCriticalError(Exception e) {
        LOGGER.log(Level.SEVERE, "Errore critico nell'applicazione", e);
        System.err.println("ERRORE CRITICO: " + e.getMessage());
        System.exit(1);
    }

    //endregion

    //region PARSING E VALIDAZIONE PARAMETRI

    /**
     * Analizza e valida i parametri della linea di comando.
     * Costruisce configurazione completa con tutte le opzioni validate.
     *
     * @param args array parametri linea comando
     * @return configurazione validata o null se help/errore
     */
    private static Configuration parseCommandLineArguments(String[] args) {
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
     * Mostra la configurazione corrente per verifica utente prima dell'esecuzione.
     */
    private static void displayConfiguration(Configuration config) {
        System.out.println("\n=== CONFIGURAZIONE SOLUTORE SAT ===");
        System.out.println("Modalità: " + (config.isFileMode ? "File singolo" : "Directory batch"));
        System.out.println("Input: " + config.inputPath);
        System.out.println("Output: " + (config.outputPath != null ? config.outputPath : "Default (stessa cartella input)"));
        System.out.println("Timeout: " + config.timeoutSeconds + " secondi");

        // Visualizza ottimizzazioni attive
        List<String> activeOpts = buildActiveOptimizationsList(config);
        System.out.println("Ottimizzazioni: " + (activeOpts.isEmpty() ? "Nessuna" : String.join(", ", activeOpts)));
        System.out.println("====================================\n");
    }

    /**
     * Costruisce lista ottimizzazioni attive per visualizzazione.
     */
    private static List<String> buildActiveOptimizationsList(Configuration config) {
        List<String> activeOpts = new ArrayList<>();
        if (config.useTseitin) activeOpts.add("Tseitin");
        if (config.useSubsumption) activeOpts.add("Sussunzione");
        if (config.useWatchedLiterals) activeOpts.add("Watched Literals");
        if (config.useRestart) activeOpts.add("Restart");
        return activeOpts;
    }

    //endregion

    //region ELABORAZIONE FILE SINGOLO

    /**
     * Elabora un singolo file contenente una formula logica attraverso la pipeline completa SAT.
     *
     * PIPELINE ELABORAZIONE:
     * 1. Lettura e parsing formula logica
     * 2. Conversione in CNF standard
     * 3. Applicazione ottimizzazioni opzionali (Tseitin, Sussunzione)
     * 4. Risoluzione SAT con algoritmo CDCL (con restart opzionale)
     * 5. Generazione output strutturato (risultati, prove, statistiche)
     *
     * @param config configurazione completa elaborazione
     */
    private static void processSingleFile(Configuration config) {
        System.out.println("\n=== ELABORAZIONE FILE ===");
        System.out.println("File: " + Paths.get(config.inputPath).getFileName());

        List<String> activeOpts = buildActiveOptimizationsList(config);
        System.out.println("Ottimizzazioni: " + (activeOpts.isEmpty() ? "Nessuna" : String.join(", ", activeOpts)));
        System.out.println("========================\n");

        try {
            // Pipeline di conversione formula
            FormulaProcessingResult formulaResult = processFormulaConversionPipeline(config);

            // Risoluzione SAT con timeout e restart
            SATResult satResult = executeSATSolving(formulaResult.finalFormula, config.timeoutSeconds, config.useRestart);

            // Gestione risultato finale
            if (satResult == null) {
                handleTimeoutResult(config);
            } else {
                handleSuccessfulResult(satResult, formulaResult, config);
            }

        } catch (Exception e) {
            handleFileProcessingError(config.inputPath, e);
        }
    }

    /**
     * Esegue la pipeline completa di conversione della formula.
     * Coordina conversione CNF e applicazione ottimizzazioni opzionali.
     *
     * @param config configurazione elaborazione
     * @return risultato processamento con formula finale e informazioni
     */
    private static FormulaProcessingResult processFormulaConversionPipeline(Configuration config) throws Exception {
        // Step 1: Lettura e conversione CNF base
        String formulaText = readFormulaFromFile(config.inputPath);
        CNFConversionResult cnfResult = convertToCNF(formulaText);
        saveCNFToFile(cnfResult.cnfString, config.inputPath, config.outputPath);

        CNFConverter finalFormula = cnfResult.cnfFormula;
        StringBuilder conversionInfo = new StringBuilder();
        boolean isECNF = false;

        // Step 2: Applicazione ottimizzazione Tseitin (opzionale)
        if (config.useTseitin) {
            TseitinConversionResult tseitinResult = applyTseitinOptimization(cnfResult);
            finalFormula = tseitinResult.ecnfFormula;
            conversionInfo.append(tseitinResult.conversionInfo);
            isECNF = true;

            saveECNFToFile(tseitinResult.ecnfString, config.inputPath, config.outputPath);
            saveTseitinStatsToFile(tseitinResult.conversionInfo, config.inputPath, config.outputPath);
        }

        // Step 3: Applicazione principio sussunzione (opzionale)
        if (config.useSubsumption) {
            SubsumptionOptimizationResult subsumptionResult = applySubsumptionOptimization(finalFormula, isECNF);
            finalFormula = subsumptionResult.optimizedFormula;
            conversionInfo.append(subsumptionResult.optimizationInfo);

            saveSubsumptionStatsToFile(subsumptionResult.optimizationInfo, config.inputPath, config.outputPath, isECNF);
        }

        // Step 4: Salvataggio file opzioni attive
        saveActiveOptionsFile(config, config.inputPath, config.outputPath);

        return new FormulaProcessingResult(finalFormula, conversionInfo.toString(), isECNF);
    }

    /**
     * Gestisce risultato di elaborazione riuscita con generazione output completo.
     */
    private static void handleSuccessfulResult(SATResult satResult, FormulaProcessingResult formulaResult, Configuration config) throws IOException {
        saveCompleteResults(satResult, formulaResult.finalFormula, config.inputPath, config.outputPath, formulaResult.conversionInfo, config);
        displayFinalStatistics(satResult, formulaResult.finalFormula);

        // NUOVO: Salva statistiche restart se abilitato
        if (config.useRestart && satResult.getStatistics().getRestarts() > 0) {
            saveRestartStatistics(satResult, config.inputPath, config.outputPath);
        }
    }

    /**
     * Gestisce caso di timeout durante risoluzione SAT.
     */
    private static void handleTimeoutResult(Configuration config) throws IOException {
        System.out.println("TIMEOUT: Superato il limite di " + config.timeoutSeconds + " secondi");
        saveTimeoutResult(config.inputPath, config.outputPath, config.timeoutSeconds, config);
    }

    /**
     * Gestisce errori durante elaborazione file con logging appropriato.
     */
    private static void handleFileProcessingError(String filePath, Exception e) {
        LOGGER.log(Level.SEVERE, "Errore elaborazione file: " + filePath, e);
        System.out.println("Errore durante l'elaborazione: " + e.getMessage());
    }

    //endregion

    //region PIPELINE CONVERSIONE FORMULA

    /**
     * Legge il contenuto di una formula logica da file con validazione.
     */
    private static String readFormulaFromFile(String filePath) throws IOException {
        System.out.println("1. Lettura formula logica...");
        String content = Files.readString(Path.of(filePath)).trim();
        LOGGER.info("Formula letta: " + content);
        return content;
    }

    /**
     * Converte formula da notazione infix a CNF usando pipeline ANTLR.
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
     * Applica ottimizzazione Tseitin per conversione in E-CNF.
     */
    private static TseitinConversionResult applyTseitinOptimization(CNFConversionResult cnfResult) throws Exception {
        System.out.println("3a. Conversione Tseitin in E-CNF...");

        TseitinConverter tseitinConverter = new TseitinConverter();
        CNFConverter ecnfFormula = tseitinConverter.convertToECNF(cnfResult.cnfFormula);
        String ecnfString = ecnfFormula.toString();
        String conversionInfo = tseitinConverter.getConversionInfo();

        LOGGER.info("Formula E-CNF generata: " + ecnfString);
        return new TseitinConversionResult(ecnfFormula, ecnfString, conversionInfo);
    }

    /**
     * Applica principio di sussunzione per eliminazione clausole ridondanti.
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

    //endregion

    //region RISOLUZIONE SAT

    /**
     * Esegue risoluzione SAT con algoritmo CDCL e gestione timeout.
     * Utilizza ExecutorService per controllo temporale e interruzione sicura.
     *
     * @param cnfFormula formula CNF da risolvere
     * @param timeoutSeconds timeout massimo in secondi
     * @param useRestart flag per abilitare tecnica restart
     * @return risultato SAT o null se timeout
     */
    private static SATResult executeSATSolving(CNFConverter cnfFormula, int timeoutSeconds, boolean useRestart) {
        String restartInfo = useRestart ? " con restart" : "";
        System.out.println("4. Risoluzione SAT con CDCL" + restartInfo + " (timeout: " + timeoutSeconds + "s)...");

        ExecutorService executor = Executors.newSingleThreadExecutor();
        CDCLSolver solver = new CDCLSolver(cnfFormula, useRestart);

        try {
            Callable<SATResult> solverTask = solver::solve;
            Future<SATResult> future = executor.submit(solverTask);
            return future.get(timeoutSeconds, TimeUnit.SECONDS);

        } catch (TimeoutException e) {
            LOGGER.warning("Timeout raggiunto dopo " + timeoutSeconds + " secondi");
            return null;

        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Errore durante risoluzione SAT", e);
            throw new RuntimeException("Errore nella risoluzione SAT", e);

        } finally {
            executor.shutdownNow();
        }
    }

    // Overload per compatibilità
    private static SATResult executeSATSolving(CNFConverter cnfFormula, int timeoutSeconds) {
        return executeSATSolving(cnfFormula, timeoutSeconds, false);
    }

    //endregion

    //region ELABORAZIONE DIRECTORY BATCH

    /**
     * Elabora tutti i file .txt in una directory con processing batch parallelo.
     * Fornisce statistiche aggregate e gestione errori per singoli file.
     */
    private static void processDirectoryBatch(Configuration config) {
        LOGGER.info("Inizio elaborazione directory: " + config.inputPath);

        if (!validateInputDirectory(config.inputPath)) return;

        try {
            List<File> txtFiles = collectTxtFiles(config.inputPath);
            if (txtFiles.isEmpty()) {
                System.out.println("Nessun file .txt trovato nella directory specificata.");
                return;
            }

            BatchResult batchResult = executeBatchProcessing(txtFiles, config);
            displayBatchSummary(batchResult);

        } catch (IOException e) {
            LOGGER.log(Level.SEVERE, "Errore accesso directory", e);
            System.out.println("Errore durante l'accesso alla directory: " + e.getMessage());
        }
    }

    /**
     * Raccoglie tutti i file .txt dalla directory con ordinamento alfabetico.
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
     * Esegue elaborazione batch sequenziale con gestione errori isolata per ogni file.
     */
    private static BatchResult executeBatchProcessing(List<File> files, Configuration config) {
        BatchResult result = new BatchResult(files.size());

        System.out.println("Timeout per file: " + config.timeoutSeconds + " secondi");
        List<String> activeOpts = buildActiveOptimizationsList(config);
        System.out.println("Ottimizzazioni: " + (activeOpts.isEmpty() ? "Nessuna" : String.join(", ", activeOpts)) + "\n");

        for (File file : files) {
            try {
                System.out.println("Elaborazione: " + file.getName());

                // Crea configurazione temporanea per il file corrente
                Configuration fileConfig = new Configuration(
                        file.getAbsolutePath(), config.outputPath, true, config.timeoutSeconds,
                        config.useTseitin, config.useSubsumption, config.useWatchedLiterals, config.useRestart);

                processSingleFile(fileConfig);
                result.incrementSuccess();

            } catch (Exception e) {
                LOGGER.log(Level.WARNING, "Errore file: " + file.getName(), e);
                System.out.println("Errore: " + e.getMessage());
                result.incrementError();
            }

            System.out.println(); // Separatore visivo
        }

        return result;
    }

    /**
     * Valida accessibilità e permessi directory di input.
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

    //endregion

    //region SALVATAGGIO E GESTIONE OUTPUT

    /**
     * Salva formula CNF in file dedicato per tracciabilità conversione.
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
     * Salva formula E-CNF (Tseitin) in file dedicato.
     */
    private static void saveECNFToFile(String ecnfString, String originalFilePath, String outputPath) throws IOException {
        System.out.println("3b. Salvataggio formula E-CNF...");

        Path ecnfDir = getECNFDirectory(originalFilePath, outputPath);
        Files.createDirectories(ecnfDir);

        String baseFileName = getBaseFileName(originalFilePath);
        Path ecnfFilePath = ecnfDir.resolve(baseFileName + ".ecnf");

        try (FileWriter writer = new FileWriter(ecnfFilePath.toFile())) {
            writer.write(ecnfString);
        }

        LOGGER.info("Formula E-CNF salvata: " + ecnfFilePath);
    }

    /**
     * Salva statistiche di conversione Tseitin in file separato.
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
     * Salva statistiche di ottimizzazione sussunzione.
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
     * NUOVO: Salva statistiche dettagliate restart in directory STATS/RESTART.
     */
    private static void saveRestartStatistics(SATResult result, String originalFilePath, String outputPath) throws IOException {
        System.out.println("5a. Salvataggio statistiche restart...");

        Path restartStatsDir = getStatsDirectory(originalFilePath, outputPath).resolve("RESTART");
        Files.createDirectories(restartStatsDir);

        String baseFileName = getBaseFileName(originalFilePath);
        Path statsFilePath = restartStatsDir.resolve(baseFileName + ".stats");

        try (FileWriter writer = new FileWriter(statsFilePath.toFile())) {
            writeRestartStatistics(writer, result);
        }

        LOGGER.info("Statistiche restart salvate: " + statsFilePath);
    }

    /**
     * NUOVO: Scrive statistiche restart dettagliate nel file.
     */
    private static void writeRestartStatistics(FileWriter writer, SATResult result) throws IOException {
        SATStatistics stats = result.getStatistics();

        writer.write("=================================\n");
        writer.write("| STATISTICHE TECNICA RESTART  |\n");
        writer.write("=================================\n\n");

        // Statistiche generali
        writer.write("STATISTICHE GENERALI:\n");
        writer.write("- Restart eseguiti: " + stats.getRestarts() + "\n");
        writer.write("- Conflitti totali: " + stats.getConflicts() + "\n");
        writer.write("- Decisioni totali: " + stats.getDecisions() + "\n");
        writer.write("- Clausole apprese: " + stats.getLearnedClauses() + "\n");

        if (stats.getRestarts() > 0) {
            double conflictsPerRestart = (double) stats.getConflicts() / stats.getRestarts();
            writer.write("- Media conflitti per restart: " + String.format("%.1f", conflictsPerRestart) + "\n");
        }

        writer.write("\n");

        // Informazioni tecniche
        writer.write("INFORMAZIONI TECNICHE:\n");
        writer.write("- Soglia restart: 5 conflitti\n");
        writer.write("- Sussunzione post-restart: ATTIVA\n");
        writer.write("- Preservazione livello 0: ATTIVA\n");
        writer.write("- Preservazione clausole apprese: ATTIVA\n");

        writer.write("\n");

        // Performance impact
        writer.write("IMPATTO PERFORMANCE:\n");
        if (stats.getRestarts() > 0) {
            writer.write("- Restart utilizzati per evitare stalli\n");
            writer.write("- Sussunzione applicata " + stats.getRestarts() + " volte\n");
            writer.write("- Formula ottimizzata ad ogni restart\n");
        } else {
            writer.write("- Nessun restart necessario\n");
            writer.write("- Risoluzione completata senza stalli\n");
        }

        writer.write("\n=================================\n");
    }

    /**
     * Salva file di riepilogo delle opzioni attive durante elaborazione.
     */
    private static void saveActiveOptionsFile(Configuration config, String originalFilePath, String outputPath) throws IOException {
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
                    writer.write("- RESTART (flag <r>): Tecniche di riavvio ogni 5 conflitti con sussunzione automatica.\n");
                }
            }

            LOGGER.info("File opzioni attive salvato: " + optionsFilePath);
        }
    }

    /**
     * Salva risultati SAT completi con modello o prova.
     */
    private static void saveCompleteResults(SATResult result, CNFConverter cnfFormula,
                                            String originalFilePath, String outputPath,
                                            String conversionInfo, Configuration config) throws IOException {
        System.out.println("5. Salvataggio risultati...");

        Path resultDir = getResultDirectory(originalFilePath, outputPath);
        Files.createDirectories(resultDir);

        String baseFileName = getBaseFileName(originalFilePath);
        Path resultFilePath = resultDir.resolve(baseFileName + ".result");

        try (FileWriter writer = new FileWriter(resultFilePath.toFile())) {
            writeStructuredResult(writer, result, originalFilePath, conversionInfo, config);
        }

        LOGGER.info("Risultati salvati: " + resultFilePath);
    }

    /**
     * Scrive risultato SAT strutturato con header e sezioni organizzate.
     */
    private static void writeStructuredResult(FileWriter writer, SATResult result,
                                              String originalFilePath, String conversionInfo, Configuration config) throws IOException {
        // Header del report
        writer.write("-------------------\n");
        writer.write("| RISOLUZIONE SAT |\n");
        writer.write("-------------------\n");
        writer.write("-> File originale: " + Paths.get(originalFilePath).getFileName() + "\n");
        writer.write("-> File CNF: " + getBaseFileName(originalFilePath) + ".cnf\n");

        if (config.useTseitin) {
            writer.write("-> File E-CNF: " + getBaseFileName(originalFilePath) + ".ecnf\n");
            writer.write("\nÈ stato utilizzato il solutore SAT sulla formula presente in " + getBaseFileName(originalFilePath) + ".ecnf\n");
        } else {
            writer.write("\nÈ stato utilizzato il solutore SAT sulla formula presente in " + getBaseFileName(originalFilePath) + ".cnf\n");
        }

        // Informazioni ottimizzazioni attive
        List<String> activeOpts = buildActiveOptimizationsList(config);
        if (!activeOpts.isEmpty()) {
            writer.write("-> Opzioni abilitate: " + String.join(", ", activeOpts) + "\n");
        }

        writer.write("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n");

        // Contenuto principale
        if (result.isSatisfiable()) {
            writeSATResult(writer, result, config.useTseitin);
        } else {
            writeUNSATResult(writer, result, config.useTseitin);
        }

        // Statistiche finali - MODIFICATO: diverse per SAT e UNSAT
        writer.write("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n");
        SATStatistics stats = result.getStatistics();

        if (result.isSatisfiable()) {
            // Per formule SAT: decisioni, propagazioni, conflitti, clausole apprese, tempo
            writer.write("Decisioni: " + stats.getDecisions() + "\n");
            writer.write("Propagazioni: " + stats.getPropagations() + "\n");
            writer.write("Conflitti: " + stats.getConflicts() + "\n");
            writer.write("Clausole apprese: " + stats.getLearnedClauses() + "\n");
            writer.write("Tempo risoluzione: " + stats.getExecutionTimeMs() + " ms\n");
        } else {
            // Per formule UNSAT: solo conflitti, clausole apprese, tempo
            writer.write("Conflitti: " + stats.getConflicts() + "\n");
            writer.write("Clausole apprese: " + stats.getLearnedClauses() + "\n");
            writer.write("Tempo risoluzione: " + stats.getExecutionTimeMs() + " ms\n");
        }
    }

    /**
     * Scrive risultato SAT con modello delle variabili.
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
     * Scrive risultato UNSAT con prova di risoluzione.
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

    /**
     * Salva report specifico per casi di timeout.
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
                writer.write("\nÈ stato utilizzato il solutore SAT sulla formula presente in " + baseFileName + ".ecnf\n");
            } else {
                writer.write("\nÈ stato utilizzato il solutore SAT sulla formula presente in " + baseFileName + ".cnf\n");
            }

            // Informazioni ottimizzazioni attive
            List<String> activeOpts = buildActiveOptimizationsList(config);
            if (!activeOpts.isEmpty()) {
                writer.write("-> Opzioni abilitate: " + String.join(", ", activeOpts) + "\n");
            }

            writer.write("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n");
            writer.write("La risoluzione ha superato il tempo limite di " + timeoutSeconds + " secondi.\n");
            writer.write("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n");
            writer.write("Decisioni effettuate: N/A\n");
            writer.write("Conflitti: N/A\n");
            writer.write("Propagazioni: N/A\n");
            writer.write("Clausole apprese: N/A\n");

            if (config.useRestart) {
                writer.write("Restart eseguiti: N/A\n");
            }

            writer.write("Tempo risoluzione: TIMEOUT\n");
        }
    }

    //endregion

    //region UTILITÀ GESTIONE PERCORSI E FILE

    /**
     * Ottiene directory per file CNF con creazione automatica struttura.
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
     * Ottiene directory per file E-CNF con creazione automatica struttura.
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
     * Ottiene directory per file statistiche con creazione automatica struttura.
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
     * Ottiene directory per file risultati con creazione automatica struttura.
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
     * Estrae nome base del file senza estensione per denominazione output.
     */
    private static String getBaseFileName(String filePath) {
        String fileName = Paths.get(filePath).getFileName().toString();
        return fileName.substring(0, fileName.lastIndexOf('.'));
    }

    //endregion

    //region STATISTICHE E VISUALIZZAZIONE

    /**
     * Visualizza statistiche finali dettagliate per elaborazione singolo file.
     */
    private static void displayFinalStatistics(SATResult result, CNFConverter cnfFormula) {
        System.out.println("6. Elaborazione completata!\n");

        String resultStr = result.isSatisfiable() ? "SAT" : "UNSAT";
        int variableCount = extractVariableCount(cnfFormula);
        int clauseCount = extractClauseCount(cnfFormula);

        result.getStatistics().printDetailedStats(variableCount, clauseCount, resultStr);
    }

    /**
     * Mostra riepilogo completo per elaborazione batch directory.
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

    /**
     * Estrae numero di variabili uniche dalla formula CNF.
     */
    private static int extractVariableCount(CNFConverter cnfFormula) {
        Set<String> variables = new HashSet<>();
        collectVariablesRecursively(cnfFormula, variables);
        return variables.size();
    }

    /**
     * Raccoglie ricorsivamente tutte le variabili dalla formula.
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
     * Estrae numero di clausole dalla formula CNF.
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

    //endregion

    //region HELP E DOCUMENTAZIONE

    /**
     * Visualizza informazioni di help complete con esempi di utilizzo.
     */
    private static void printHelp() {
        System.out.println("\n=== SOLUTORE SAT CDCL v1.8.0 ===");
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
        System.out.println("                  r = Tecniche di restart (ogni 5 conflitti)");
        System.out.println("                  t = Trasformazione di Tseitin");
        System.out.println("                  all = Tutte le ottimizzazioni");
        System.out.println("  -h              Mostra questa guida\n");

        System.out.println("ESEMPI:");
        System.out.println("  java -jar solutore_SAT.jar -f formula.txt");
        System.out.println("  java -jar solutore_SAT.jar -f formula.txt -opt=r");
        System.out.println("  java -jar solutore_SAT.jar -f formula.txt -opt=st");
        System.out.println("  java -jar solutore_SAT.jar -f formula.txt -opt=str");
        System.out.println("  java -jar solutore_SAT.jar -f formula.txt -opt=all");
        System.out.println("  java -jar solutore_SAT.jar -d ./formule/ -o ./risultati/ -t 30 -opt=sr");
        System.out.println("  java -jar solutore_SAT.jar -d ./formule/ -opt=rt -t 60\n");

        System.out.println("NOTE:");
        System.out.println("  • Le opzioni -f e -d sono mutuamente esclusive");
        System.out.println("  • Il solver supporta formule con operatori: AND, OR, NOT, ->, <->");
        System.out.println("  • Output automatico: file .cnf e .result nelle directory CNF/ e RESULT/");
        System.out.println("  • Con ottimizzazioni attive:");
        System.out.println("    - File .ecnf nella directory E-CNF/ (con -opt=t)");
        System.out.println("    - Statistiche organizzate in STATS/TSEITIN/, STATS/SUBSUMPTION/, STATS/RESTART/");
        System.out.println("    - File opzioni_attive.txt nella directory STATS/");
        System.out.println("  • Tseitin è raccomandato per formule complesse (>8 operatori)");
        System.out.println("  • Sussunzione elimina clausole ridondanti che sono sovrainsieme di altre");
        System.out.println("  • Restart applica reinizio ogni 5 conflitti con sussunzione automatica\n");
        System.out.println("=====================================\n");
    }

    //endregion

    //region CLASSI DI CONFIGURAZIONE E SUPPORTO

    /**
     * Configurazione validata dell'applicazione contenente tutti i parametri di esecuzione.
     * Immutable dopo costruzione per garantire thread-safety e consistenza.
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
     * Parser avanzato per parametri linea di comando con validazione completa.
     * Gestisce tutti i casi edge e fornisce messaggi di errore informativi.
     */
    private static class CommandLineParser {

        /**
         * Analizza e valida tutti i parametri forniti costruendo configurazione completa.
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

            if (inputPath == null) {
                throw new IllegalArgumentException("Specificare un file (-f) o directory (-d)");
            }

            return new Configuration(inputPath, outputPath, isFileMode, timeoutSeconds,
                    useTseitin, useSubsumption, useWatchedLiterals, useRestart);
        }

        /**
         * Parsa flag di ottimizzazione con gestione valori speciali.
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
                tseitin = true;
                subsumption = true;
                watchedLiterals = true;
                restart = true;
            } else {
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
         * Estrae prossimo argomento con validazione presenza.
         */
        private String getNextArgument(String[] args, int currentIndex, String argumentType) {
            if (currentIndex + 1 >= args.length) {
                throw new IllegalArgumentException("Parametro " + args[currentIndex] +
                        " richiede " + argumentType);
            }
            return args[currentIndex + 1];
        }

        /**
         * Valida e converte timeout con controlli range.
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
         * Valida esistenza e accessibilità file.
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
         * Valida esistenza e accessibilità directory.
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
         * Valida o crea directory di output con permessi.
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
     * Flag di ottimizzazione parsate dalla linea di comando.
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
     * Risultato di elaborazione batch con statistiche aggregate.
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
     * Risultato conversione CNF base con formula e rappresentazione stringa.
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
     * Risultato conversione Tseitin completa con informazioni dettagliate.
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
     * Risultato ottimizzazione sussunzione con formula e statistiche.
     */
    private static class SubsumptionOptimizationResult {
        final CNFConverter optimizedFormula;
        final String optimizationInfo;

        SubsumptionOptimizationResult(CNFConverter optimizedFormula, String optimizationInfo) {
            this.optimizedFormula = optimizedFormula;
            this.optimizationInfo = optimizationInfo;
        }
    }

    /**
     * Risultato completo di processamento formula con metadata.
     */
    private static class FormulaProcessingResult {
        final CNFConverter finalFormula;
        final String conversionInfo;
        final boolean isECNF;

        FormulaProcessingResult(CNFConverter finalFormula, String conversionInfo, boolean isECNF) {
            this.finalFormula = finalFormula;
            this.conversionInfo = conversionInfo;
            this.isECNF = isECNF;
        }
    }

    //endregion
}