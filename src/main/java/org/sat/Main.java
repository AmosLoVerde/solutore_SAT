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
import org.sat.optionalfeatures.PigeonholeProblem;
import org.sat.optionalfeatures.StandardConverterCNF;
import org.sat.optionalfeatures.SubsumptionPrinciple;
import org.sat.optionalfeatures.TseitinConverter;
import org.sat.support.CNFFormula;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.concurrent.*;

/**
 * SOLUTORE SAT CDCL (Conflict-Driven Clause Learning)
 *
 * PIPELINE DI ELABORAZIONE COMPLETA:
 * 1. INPUT: Formula logica da file di testo o file CNF standard
 * 2. PARSING: Conversione notazione infissa -> albero sintattico (ANTLR) o parsing CNF diretto
 * 3. CONVERSIONE IN CNF: Trasformazione in Forma Normale Congiuntiva standard
 * 4. OPZIONI FACOLTATIVE:
 *    - Tseitin: Conversione E-CNF equisoddisfacibile
 *    - Sussunzione: Eliminazione clausole ridondanti (sovrainsieme)
 *    - Reinizio: Reinizio periodico a ogni 5 conflitti + sussunzione automatica
 *    - Convert: Modalità diretta per file già in formato CNF
 * 5. RISOLUZIONE SAT: Si utilizza l'algoritmo CDCL + euristiche VSIDS
 * 6. OUTPUT: Risultati strutturati, prove UNSAT, statistiche performance
 *
 * MODALITÀ OPERATIVE SUPPORTATE:
 * - File singolo (-f): Elaborazione di un singolo file .txt o .cnf
 * - Directory batch (-d): Elaborazione automatica di tutti i file .txt/.cnf in una cartella
 * - Configurazione opzioni tramite flag (-opt=<flag>, -opt=all)
 * - Timeout configurabile per evitare elaborazioni troppo dispendiose (-t secondi)
 * - Output directory personalizzabile per organizzazione risultati (-o directory)
 * - Generazione istanze Pigeonhole Problem (-gen=pigeonhole <numero>)
 * - Conversione diretta CNF (-convert per file .cnf)
 *
 * ORGANIZZAZIONE DEGLI OUTPUT STRUTTURATI:
 * - CNF/: Formule convertite in Forma Normale Congiuntiva (non creata in modalità -convert)
 * - E-CNF/: Formule Tseitin equisoddisfacibili (se si attiva -opt=t)
 * - RESULT/: Risultati SAT/UNSAT con modelli e prove matematiche
 * - STATS/: Statistiche dettagliate suddivise per tipologia ottimizzazione
 * - PIGEONHOLE/: Istanze generate del Pigeonhole Problem (se si attiva -gen=pigeonhole)
 *
 * @author Amos Lo Verde
 * @version 1.10.0
 */
public final class Main {
    //region CONFIGURAZIONE PARAMETRI APPLICAZIONE

    /**
     * Parametri linea di comando supportati
     * */
    private static final String HELP_PARAM = "-h";
    private static final String FILE_PARAM = "-f";
    private static final String DIR_PARAM = "-d";
    private static final String OUTPUT_PARAM = "-o";
    private static final String TIMEOUT_PARAM = "-t";
    private static final String OPT_PARAM = "-opt=";
    private static final String GEN_PARAM = "-gen=";
    private static final String CONVERT_PARAM = "-convert";

    /**
     * Flag ottimizzazioni disponibili
     * */
    private static final String OPT_SUBSUMPTION = "s";
    private static final String OPT_RESTART = "r";
    private static final String OPT_TSEITIN = "t";
    private static final String OPT_ALL = "all";

    /**
     * Flag generazione problemi disponibili
     * */
    private static final String GEN_PIGEONHOLE = "pigeonhole";

    /**
     * Configurazioni timeout di default e limiti
     * */
    private static final int DEFAULT_TIMEOUT_SECONDS = 10;
    private static final int MIN_TIMEOUT_SECONDS = 5;

    /**
     * Limiti per generazione istanze
     * */
    private static final int MIN_PIGEONHOLE_INSTANCES = 1;
    private static final int MAX_PIGEONHOLE_INSTANCES = 100;

    /**
     * Previene istanziazione - classe utility
     * */
    private Main() {
        throw new UnsupportedOperationException("Classe utility non istanziabile");
    }

    //endregion

    //region PUNTO PRINCIPALE

    /**
     * Punto principale dell'applicazione SAT solver.
     *
     * Coordina l'intero flusso di esecuzione dall'analisi dei parametri alla
     * generazione dei risultati finali, gestendo errori e cleanup automatico.
     *
     * FLUSSO ESECUZIONE:
     * 1. Parsing e validazione parametri linea di comando
     * 2. Configurazione ambiente di esecuzione (timeout, ottimizzazioni)
     * 3. Utilizzo della modalità appropriata (file singolo, directory, generazione, o conversione)
     * 4. Gestione errori globali e pulizia finale delle risorse
     *
     * @param args parametri linea di comando forniti dall'utente
     */
    public static void main(String[] args) {
        System.out.println("---> AVVIO SOLUTORE SAT CDCL <---");

        try {
            // Validazione input utente
            if (args.length == 0) {
                System.out.println("[E] Nessun parametro fornito. Usa -h per visualizzare l'help.");
                return;
            }

            // Parsing e validazione parametri
            SolverConfiguration config = parseAndValidateArguments(args);
            if (config == null) return; // Help mostrato o errore

            // Esecuzione pipeline principale
            displayConfigurationSummary(config);
            executeMainPipeline(config);

        } catch (Exception e) {
            handleGlobalError(e);
        } finally {
            System.out.println("---> FINE ESECUZIONE SOLUTORE SAT <---");
        }
    }

    /**
     * Esegue la pipeline principale di elaborazione basata sulla configurazione.
     *
     * Determina automaticamente la modalità operativa (file singolo, directory, conversione, o generazione)
     * e delega all'handler appropriato per l'esecuzione specializzata.
     *
     * @param config configurazione validata contenente tutti i parametri
     */
    private static void executeMainPipeline(SolverConfiguration config) {
        if (config.isGenerationMode) {
            System.out.println("[I] Modalità: Generazione istanze " + config.generationType);
            // Processatore generazione istanze
            processInstanceGeneration(config);
        } else if (config.isConvertMode) {
            System.out.println("[I] Modalità: Conversione diretta CNF");
            // Processatore conversione diretta CNF
            if (config.isFileMode) {
                processConvertSingleFile(config);
            } else {
                processConvertDirectoryBatch(config);
            }
        } else if (config.isFileMode) {
            System.out.println("[I] Modalità: Elaborazione file singolo");
            // Processatore del file singolo
            processSingleFile(config);
        } else {
            System.out.println("[I] Modalità: Elaborazione della directory");
            // Processatore dei file interni alla directory
            processDirectoryBatch(config);
        }
    }

    /**
     * Gestisce errori critici dell'applicazione con logging completo.
     *
     * Registra errori nel sistema di logging e fornisce feedback utente
     * appropriato prima di terminare l'esecuzione con codice di errore.
     *
     * @param e eccezione critica che ha causato il fallimento
     */
    private static void handleGlobalError(Exception e) {
        System.out.println("[E] Errore critico nell'applicazione: " + e.getMessage());
        System.out.println("Controllare i log per dettagli completi.");
        System.exit(1);
    }

    //endregion

    //region PARSING E VALIDAZIONE PARAMETRI

    /**
     * Analizza e valida tutti i parametri della linea di comando.
     *
     * Processa sequenzialmente ogni parametro, applicando validazioni specifiche
     * e costruendo una configurazione completa. Gestisce conflitti tra parametri
     * e fornisce messaggi di errore informativi per input non validi.
     *
     * @param args array di parametri da processare
     * @return configurazione validata o null se help/errore
     */
    private static SolverConfiguration parseAndValidateArguments(String[] args) {
        try {
            ArgumentParser parser = new ArgumentParser();
            // Ritorna il parser degli argomenti
            return parser.parse(args);
        } catch (IllegalArgumentException e) {
            System.out.println("[E] Errore nella validazione dei parametri:: " + e.getMessage());
            System.out.println("Usa -h per visualizzare l'help completo.");
            return null;
        }
    }

    /**
     * Visualizza il riepilogo della configurazione prima dell'esecuzione.
     *
     * @param config configurazione da visualizzare
     */
    private static void displayConfigurationSummary(SolverConfiguration config) {
        System.out.println("\n-->> CONFIGURAZIONE SOLUTORE SAT <<--");

        if (config.isGenerationMode) {
            System.out.println("Modalità: Generazione istanze " + config.generationType);
            System.out.println("Numero istanze: " + config.generationCount);
        } else if (config.isConvertMode) {
            System.out.println("Modalità: Conversione diretta CNF");
            System.out.println("Input: " + config.inputPath);
            System.out.println("Formato: File .cnf");
            System.out.println("Timeout: " + config.timeoutSeconds + " secondi");

            // Mostra le opzioni aggiuntive: tseitin, sussunzione, reinizio
            List<String> activeOpts = buildActiveOptimizationsList(config);
            System.out.println("Opzioni aggiuntive: " + (activeOpts.isEmpty() ? "Nessuna" : String.join(", ", activeOpts)));
        } else {
            System.out.println("Modalità: " + (config.isFileMode ? "File singolo" : "Directory"));
            System.out.println("Input: " + config.inputPath);
            System.out.println("Timeout: " + config.timeoutSeconds + " secondi");

            // Mostra le opzioni aggiuntive: tseitin, sussunzione, reinizio
            List<String> activeOpts = buildActiveOptimizationsList(config);
            System.out.println("Opzioni aggiuntive: " + (activeOpts.isEmpty() ? "Nessuna" : String.join(", ", activeOpts)));
        }

        System.out.println("Output: " + (config.outputPath != null ? config.outputPath : "Directory input"));
        System.out.println("====================================\n");
    }

    /**
     * Costruisce lista delle ottimizzazioni attive per visualizzazione.
     *
     * @param config configurazione da analizzare
     * @return lista nomi ottimizzazioni attive
     */
    private static List<String> buildActiveOptimizationsList(SolverConfiguration config) {
        List<String> activeOpts = new ArrayList<>();
        if (config.useTseitin) activeOpts.add("Tseitin");
        if (config.useSubsumption) activeOpts.add("Sussunzione");
        if (config.useRestart) activeOpts.add("Restart");
        return activeOpts;
    }

    //endregion

    //region GENERAZIONE ISTANZE

    /**
     * Processa richiesta di generazione istanze per problemi specifici.
     *
     * @param config configurazione contenente tipo generazione e parametri
     */
    private static void processInstanceGeneration(SolverConfiguration config) {
        System.out.println("-->> GENERAZIONE ISTANZE <<--");
        System.out.println("Tipo: " + config.generationType);
        System.out.println("Numero istanze: " + config.generationCount);
        System.out.println("=========================\n");

        try {
            switch (config.generationType) {
                case GEN_PIGEONHOLE -> {
                    generatePigeonholeInstances(config);
                }
                default -> {
                    throw new IllegalArgumentException("Tipo generazione non supportato: " + config.generationType);
                }
            }

            System.out.println("[I] Generazione istanze completata con successo!");

        } catch (Exception e) {
            handleGenerationError(config.generationType, e);
        }
    }

    /**
     * Genera istanze del Pigeonhole Problem utilizzando il generatore dedicato.
     *
     * @param config configurazione con parametri generazione
     */
    private static void generatePigeonholeInstances(SolverConfiguration config) {
        System.out.println("Generazione " + config.generationCount + " istanze Pigeonhole Problem...");

        // Inizializza generatore
        PigeonholeProblem generator = new PigeonholeProblem();

        // Configura directory output
        String outputDir = config.outputPath != null ? config.outputPath : ".";
        generator.setOutputDirectory(outputDir);

        // Genera istanze
        generator.generateInstances(config.generationCount);

        // Mostra report finale
        System.out.println("\n[I] Report generazione:");
        System.out.println("Istanze create: " + generator.getGeneratedInstancesCount());
        System.out.println("Directory output: " + generator.getOutputDirectory());
    }

    /**
     * Gestisce errori durante generazione istanze.
     *
     * @param generationType tipo di generazione che ha causato errore
     * @param e eccezione verificatasi
     */
    private static void handleGenerationError(String generationType, Exception e) {
        System.out.println("[E] Errore durante generazione istanze " + generationType + ": " + e.getMessage());
        throw new RuntimeException("Generazione istanze fallita", e);
    }

    //endregion

    //region ELABORAZIONE CONVERSIONE DIRETTA CNF

    /**
     * Elabora un singolo file CNF attraverso conversione diretta.
     *
     * @param config configurazione contenente path file e opzioni
     */
    private static void processConvertSingleFile(SolverConfiguration config) {
        System.out.println("-->> ELABORAZIONE FILE CNF <<--");
        System.out.println("File: " + Paths.get(config.inputPath).getFileName());
        System.out.println("==============================\n");

        try {
            // Verifica estensione .cnf
            if (!config.inputPath.toLowerCase().endsWith(".cnf")) {
                throw new IllegalArgumentException("Modalità -convert richiede file con estensione .cnf, ricevuto: " + config.inputPath);
            }

            // FASE 1: Conversione diretta da formato CNF a CNFConverter
            CNFConverter cnfFormula = executeDirectCNFConversion(config.inputPath);

            // FASE 2: Applicazione opzioni facoltative (Tseitin, Sussunzione)
            FormulaProcessingResult formulaResult = applyOptionalFeaturesToCNF(cnfFormula, config);

            // FASE 3: Risoluzione SAT con timeout
            SATResult satResult = executeSATSolvingWithTimeout(formulaResult.finalFormula, config);

            // FASE 4: Gestione risultato e output
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
     * Elabora tutti i file .cnf in una directory con conversione diretta.
     *
     * @param config configurazione con directory input e opzioni
     */
    private static void processConvertDirectoryBatch(SolverConfiguration config) {
        System.out.println("[I] Inizio elaborazione directory CNF: " + config.inputPath);

        if (!validateInputDirectory(config.inputPath)) return;

        try {
            // Cerca tutti i file .cnf
            List<File> cnfFiles = findAllCnfFiles(config.inputPath);
            if (cnfFiles.isEmpty()) {
                System.out.println("[W] Nessun file .cnf trovato nella directory specificata.");
                return;
            }

            BatchResult batchResult = executeConvertBatchProcessing(cnfFiles, config);
            displayBatchSummary(batchResult);

        } catch (IOException e) {
            System.out.println("[E] Errore durante l'accesso alla directory: " + e.getMessage());
        }
    }

    /**
     * Trova tutti i file .cnf nella directory specificata.
     *
     * @param dirPath directory da scansionare
     * @return lista ordinata di file .cnf trovati
     * @throws IOException se errori di accesso alla directory
     */
    private static List<File> findAllCnfFiles(String dirPath) throws IOException {
        System.out.println("Ricerca file .cnf nella directory...");

        List<File> cnfFiles = Files.list(Paths.get(dirPath))
                .filter(path -> path.toString().toLowerCase().endsWith(".cnf"))
                .map(Path::toFile)
                .sorted(Comparator.comparing(File::getName))
                .toList();

        System.out.println("Trovati " + cnfFiles.size() + " file .cnf da elaborare.");
        return cnfFiles;
    }

    /**
     * Esegue l'elaborazione sequenziale dei file CNF con gestione degli errori isolata.
     *
     * @param files lista file da elaborare
     * @param config configurazione di base
     * @return risultati aggregati del batch
     */
    private static BatchResult executeConvertBatchProcessing(List<File> files, SolverConfiguration config) {
        BatchResult result = new BatchResult(files.size());

        System.out.println("Configurazione batch CNF:");
        System.out.println("- Timeout per file: " + config.timeoutSeconds + " secondi");
        List<String> activeOpts = buildActiveOptimizationsList(config);
        System.out.println("- Opzioni aggiuntive: " + (activeOpts.isEmpty() ? "Nessuna" : String.join(", ", activeOpts)));
        System.out.println();

        // Scorre ciascun file nella lista di tutti i file .cnf da elaborare
        for (File file : files) {
            try {
                System.out.println("Elaborazione: " + file.getName());

                // Crea configurazione specifica per questo file con modalità convert
                SolverConfiguration fileConfig = createConvertFileConfiguration(file, config);
                processConvertSingleFile(fileConfig);
                result.incrementSuccess();

            } catch (Exception e) {
                System.out.println("[E] Errore nel file " + file.getName() + ": " + e);
                result.incrementError();
            }
            System.out.println(); // Separatore visivo
        }

        return result;
    }

    /**
     * Esegue conversione diretta da file CNF standard a CNFConverter.
     *
     * @param filePath percorso del file .cnf da convertire
     * @return CNFConverter risultante dalla conversione
     * @throws Exception se errori durante conversione
     */
    private static CNFConverter executeDirectCNFConversion(String filePath) throws Exception {
        System.out.println("Conversione diretta da formato CNF standard...");

        // Utilizza StandardConverterCNF per la conversione
        StandardConverterCNF converter = new StandardConverterCNF();
        CNFConverter result = converter.convertFromStandardCNF(filePath);

        if (result.toString().length() > 100) {
            System.out.println("[I] La formula CNF convertita è troppo lunga per essere mostrata qui a schermo.");
        } else {
            System.out.println("[I] Formula CNF convertita: " + result.toString());
        }
        return result;
    }

    /**
     * Applica opzioni facoltative a una formula già in CNF.
     *
     * @param cnfFormula formula CNF di base
     * @param config configurazione con opzioni attive
     * @return risultato con formula finale e metadata
     * @throws Exception se errori durante applicazione opzioni
     */
    private static FormulaProcessingResult applyOptionalFeaturesToCNF(CNFConverter cnfFormula, SolverConfiguration config) throws Exception {
        CNFFormula initialFormula = new CNFFormula(cnfFormula);
        int initialClausesCount = initialFormula.getClausesCount();
        int initialVariablesCount = initialFormula.getVariableCount();

        CNFConverter finalFormula = cnfFormula;
        StringBuilder conversionInfo = new StringBuilder();
        boolean isECNF = false;

        // Step 1: Applicazione Tseitin (opzionale)
        if (config.useTseitin) {
            System.out.println("Applicazione trasformazione Tseitin...");
            TseitinConversionResult tseitinResult = applyTseitinTransformation(new CNFConversionResult(cnfFormula, cnfFormula.toString()));
            finalFormula = tseitinResult.ecnfFormula;
            conversionInfo.append(tseitinResult.conversionInfo);
            isECNF = true;

            // Salva il risultato E-CNF
            saveFormulaToFile(tseitinResult.ecnfString, config, "E-CNF", ".ecnf");
            saveOptimizationStats(tseitinResult.conversionInfo, config, "TSEITIN");
        }

        // Step 2: Applicazione Sussunzione (opzionale)
        if (config.useSubsumption) {
            System.out.println("Applicazione principio di sussunzione...");
            SubsumptionResult subsumptionResult = applySubsumptionOptimization(finalFormula);
            finalFormula = subsumptionResult.optimizedFormula;
            conversionInfo.append(subsumptionResult.optimizationInfo);

            saveOptimizationStats(subsumptionResult.optimizationInfo, config, "SUBSUMPTION");
        }

        // Step 3: Salvataggio opzioni attive
        saveActiveOptionsFile(config);

        return new FormulaProcessingResult(finalFormula, conversionInfo.toString(), isECNF, initialClausesCount, initialVariablesCount);
    }

    //endregion

    //region ELABORAZIONE DEL SINGOLO FILE

    /**
     * Elabora un singolo file attraverso la pipeline completa SAT.
     *
     * Esegue sequenzialmente tutte le fasi di trasformazione:
     * Lettura -> Parsing -> CNF (-> opzioni aggiuntive abilitate) -> risoluzione -> output.
     * Gestisce timeout e genera risultati strutturati.
     *
     * @param config configurazione contenente path file e opzioni
     */
    private static void processSingleFile(SolverConfiguration config) {
        System.out.println("-->> ELABORAZIONE FILE <<--");
        System.out.println("File: " + Paths.get(config.inputPath).getFileName());
        System.out.println("=========================\n");

        try {
            // FASE 1: Pipeline di conversione formula
            FormulaProcessingResult formulaResult = executeFormulaProcessingPipeline(config);

            // FASE 2: Risoluzione SAT con timeout
            SATResult satResult = executeSATSolvingWithTimeout(formulaResult.finalFormula, config);

            // FASE 3: Gestione risultato e output
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
     * Esegue la pipeline completa di trasformazione della formula.
     *
     * Coordina tutte le fasi di conversione e ottimizzazione:
     * Input -> CNF -> Tseitin (opzionale) -> Sussunzione (opzionale).
     * Salva tutti i file intermedi per tracciabilità.
     *
     * @param config configurazione con opzioni di ottimizzazione
     * @return risultato completo con formula finale e metadata
     * @throws Exception se errori durante trasformazione
     */
    private static FormulaProcessingResult executeFormulaProcessingPipeline(SolverConfiguration config) throws Exception {
        // Step 1: Lettura e conversione CNF base
        String formulaText = readFormulaFromFile(config.inputPath);
        CNFConversionResult cnfResult = convertFormulaToCNF(formulaText);

        CNFFormula initialFormula = new CNFFormula(cnfResult.cnfFormula);
        int initialClausesCount = initialFormula.getClausesCount();
        int initialVariablesCount = initialFormula.getVariableCount();

        // Scrive la formula appena trasformata nel formato .cnf dentro la cartella CNF
        saveFormulaToFile(cnfResult.cnfString, config, "CNF", ".cnf");

        CNFConverter finalFormula = cnfResult.cnfFormula;
        StringBuilder conversionInfo = new StringBuilder();
        boolean isECNF = false;     // Flag per sapere se è E-CNF, in caso si abiliti Tseitin diventa true

        // Step 2: Applicazione Tseitin (opzionale)
        if (config.useTseitin) {
            System.out.println("Applicazione trasformazione Tseitin...");
            TseitinConversionResult tseitinResult = applyTseitinTransformation(cnfResult);
            finalFormula = tseitinResult.ecnfFormula;
            conversionInfo.append(tseitinResult.conversionInfo);
            isECNF = true;      // Imposta la flag a true

            // Salva il nuovo risultato nel formato .ecnf dentro la cartella E-CNF
            saveFormulaToFile(tseitinResult.ecnfString, config, "E-CNF", ".ecnf");
            saveOptimizationStats(tseitinResult.conversionInfo, config, "TSEITIN");
        }

        // Step 3: Applicazione Sussunzione (opzionale)
        if (config.useSubsumption) {
            System.out.println("Applicazione principio di sussunzione...");
            SubsumptionResult subsumptionResult = applySubsumptionOptimization(finalFormula);
            finalFormula = subsumptionResult.optimizedFormula;
            conversionInfo.append(subsumptionResult.optimizationInfo);

            saveOptimizationStats(subsumptionResult.optimizationInfo, config, "SUBSUMPTION");
        }

        // Step 4: Salvataggio opzioni attive
        saveActiveOptionsFile(config);

        return new FormulaProcessingResult(finalFormula, conversionInfo.toString(), isECNF, initialClausesCount, initialVariablesCount);
    }

    /**
     * Esegue risoluzione SAT con gestione timeout controllata.
     *
     * Utilizza ExecutorService per controllo temporale preciso e interruzione
     * sicura del solver in caso di superamento del timeout configurato.
     *
     * @param formula formula CNF da risolvere
     * @param config configurazione con timeout e opzioni restart
     * @return risultato SAT o null se timeout
     */
    private static SATResult executeSATSolvingWithTimeout(CNFConverter formula, SolverConfiguration config) {
        String restartInfo = config.useRestart ? " con restart" : "";
        System.out.println("Risoluzione SAT con CDCL" + restartInfo + " (timeout: " + config.timeoutSeconds + "s)...");

        ExecutorService executor = Executors.newSingleThreadExecutor();
        CDCLSolver solver = new CDCLSolver(formula, config.useRestart);

        try {
            Callable<SATResult> solverTask = solver::solve;
            Future<SATResult> future = executor.submit(solverTask);
            return future.get(config.timeoutSeconds, TimeUnit.SECONDS);

        } catch (TimeoutException e) {
            System.out.println("[W] Timeout raggiunto dopo " + config.timeoutSeconds + " secondi");
            return null;
        } catch (Exception e) {
            System.out.println("[E] Errore durante risoluzione SAT: " + e);
            throw new RuntimeException("Errore nella risoluzione SAT", e);
        } finally {
            executor.shutdownNow();
        }
    }

    //endregion

    //region PIPELINE CONVERSIONE FORMULE

    /**
     * Legge il contenuto testuale di una formula logica da file.
     *
     * @param filePath percorso del file contenente la formula
     * @return contenuto della formula come stringa pulita
     * @throws IOException se errori di accesso al file
     */
    private static String readFormulaFromFile(String filePath) throws IOException {
        System.out.println("Lettura formula logica...");
        String content = Files.readString(Path.of(filePath)).trim();
        System.out.println("[I] Formula letta: " + content);
        return content;
    }

    /**
     * Converte la formula dalla notazione infissa a quella CNF usando pipeline ANTLR.
     *
     * Processo completo: Lexing -> Parsing -> Visitor Pattern -> CNF Transform.
     * Applica automaticamente tutte le trasformazioni necessarie per CNF.
     *
     * @param formulaText formula in notazione matematica standard
     * @return risultato conversione con formula CNF e rappresentazione stringa
     * @throws Exception se errori durante parsing o conversione
     */
    private static CNFConversionResult convertFormulaToCNF(String formulaText) throws Exception {
        System.out.println("Conversione in CNF...");

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

        System.out.println("[I] Formula CNF generata: " + cnfString);
        return new CNFConversionResult(cnfFormula, cnfString);
    }

    /**
     * Applica trasformazione di Tseitin per conversione in E-CNF.
     *
     * La trasformazione introduce variabili ausiliarie mantenendo
     * l'equisoddisfacibilità con la formula originale.
     *
     * @param cnfResult risultato conversione CNF di base
     * @return risultato trasformazione Tseitin con E-CNF e statistiche
     * @throws Exception se errori durante trasformazione
     */
    private static TseitinConversionResult applyTseitinTransformation(CNFConversionResult cnfResult) throws Exception {
        TseitinConverter tseitinConverter = new TseitinConverter();
        CNFConverter ecnfFormula = tseitinConverter.convertToECNF(cnfResult.cnfFormula);
        String ecnfString = ecnfFormula.toString();
        String conversionInfo = tseitinConverter.getConversionInfo();

        System.out.println("[I] Formula E-CNF generata: " + ecnfString);
        return new TseitinConversionResult(ecnfFormula, ecnfString, conversionInfo);
    }

    /**
     * Applica principio di sussunzione per eliminazione clausole ridondanti.
     *
     * Identifica e rimuove clausole che sono sovrainsieme di altre clausole,
     * riducendo la dimensione della formula senza alterare la soddisfacibilità.
     *
     * @param formula formula CNF da ottimizzare
     * @return risultato ottimizzazione con formula ridotta e statistiche
     * @throws Exception se errori durante ottimizzazione
     */
    private static SubsumptionResult applySubsumptionOptimization(CNFConverter formula) throws Exception {
        SubsumptionPrinciple subsumptionOptimizer = new SubsumptionPrinciple();
        CNFConverter optimizedFormula = subsumptionOptimizer.applySubsumption(formula);
        String optimizationInfo = subsumptionOptimizer.getOptimizationInfo();

        System.out.println("[I] Formula ottimizzata: " + optimizedFormula.toString());
        System.out.println("[I] Clausole eliminate: " + subsumptionOptimizer.getEliminatedClausesCount());

        return new SubsumptionResult(optimizedFormula, optimizationInfo);
    }

    //endregion

    //region ELABORAZIONE DELLA DIRECTORY

    /**
     * Elabora tutti i file .txt in una directory
     *
     * Trova automaticamente tutti i file .txt, li elabora sequenzialmente
     * applicando la stessa configurazione, e fornisce statistiche aggregate.
     *
     * @param config configurazione con directory input e opzioni
     */
    private static void processDirectoryBatch(SolverConfiguration config) {
        System.out.println("[I] Inizio elaborazione directory: " + config.inputPath);

        if (!validateInputDirectory(config.inputPath)) return;

        try {
            // Cerca tutti i file di testo .txt
            List<File> txtFiles = findAllTxtFiles(config.inputPath);
            if (txtFiles.isEmpty()) {
                System.out.println("[W] Nessun file .txt trovato nella directory specificata.");
                return;
            }

            BatchResult batchResult = executeBatchProcessing(txtFiles, config);
            displayBatchSummary(batchResult);

        } catch (IOException e) {
            System.out.println("[E] Errore durante l'accesso alla directory: " + e.getMessage());
        }
    }

    /**
     * Trova tutti i file .txt nella directory specificata.
     *
     * @param dirPath directory da scansionare
     * @return lista ordinata di file .txt trovati
     * @throws IOException se errori di accesso alla directory
     */
    private static List<File> findAllTxtFiles(String dirPath) throws IOException {
        System.out.println("Ricerca file .txt nella directory...");

        List<File> txtFiles = Files.list(Paths.get(dirPath))
                .filter(path -> path.toString().toLowerCase().endsWith(".txt"))
                .map(Path::toFile)
                .sorted(Comparator.comparing(File::getName))
                .toList();

        System.out.println("Trovati " + txtFiles.size() + " file .txt da elaborare.");
        return txtFiles;
    }

    /**
     * Esegue l'elaborazione sequenziale con gestione degli errori isolata.
     *
     * Ogni file viene elaborato indipendentemente. Gli errori su singoli
     * file non interrompono l'elaborazione degli altri.
     *
     * @param files lista file da elaborare
     * @param config configurazione di base
     * @return risultati aggregati del batch
     */
    private static BatchResult executeBatchProcessing(List<File> files, SolverConfiguration config) {
        BatchResult result = new BatchResult(files.size());

        System.out.println("Configurazione batch:");
        System.out.println("- Timeout per file: " + config.timeoutSeconds + " secondi");
        List<String> activeOpts = buildActiveOptimizationsList(config);
        System.out.println("- Opzioni aggiuntive: " + (activeOpts.isEmpty() ? "Nessuna" : String.join(", ", activeOpts)));
        System.out.println();

        // Scorre ciascun file nella lista di tutti i file .txt da elaborare
        for (File file : files) {
            try {
                System.out.println("Elaborazione: " + file.getName());

                // Crea configurazione specifica per questo file
                SolverConfiguration fileConfig = createFileConfiguration(file, config);
                processSingleFile(fileConfig);
                result.incrementSuccess();

            } catch (Exception e) {
                System.out.println("[E] Errore nel file " + file.getName() + ": " + e);
                result.incrementError();
            }
            System.out.println(); // Separatore visivo
        }

        return result;
    }

    /**
     * Valida l'accessibilità della directory di input.
     *
     * @param dirPath percorso directory da validare
     * @return true se directory valida e accessibile
     */
    private static boolean validateInputDirectory(String dirPath) {
        File dir = new File(dirPath);

        // Verifica l'esistenza della directory
        if (!dir.exists() || !dir.isDirectory()) {
            System.out.println("[E] Errore: directory non esistente: " + dirPath);
            return false;
        }

        // Verifica se la directory può essere letta
        if (!dir.canRead()) {
            System.out.println("[E] Errore: directory non leggibile: " + dirPath);
            return false;
        }

        return true;
    }

    /**
     * Mostra il riepilogo finale dell'elaborazione della directory.
     *
     * @param result risultati aggregati da visualizzare
     */
    private static void displayBatchSummary(BatchResult result) {
        System.out.println("\n-->> RIEPILOGO ELABORAZIONE DIRECTORY <<--");
        System.out.println("File elaborati trovati: " + result.totalFiles);
        System.out.println("File elaborati con successo: " + result.successCount);
        System.out.println("File con errori: " + result.errorCount);

        if (result.totalFiles > 0) {
            double successRate = (double) result.successCount / result.totalFiles * 100;
            System.out.printf("Tasso di successo: %.1f%%\n", successRate);
        }
        System.out.println("=========================================\n");
    }

    //endregion

    //region GESTIONE DELL'OUTPUT E SALVATAGGIO DEI FILE

    /**
     * Salva la formula in file con directory appropriata.
     *
     * @param content contenuto da salvare
     * @param config configurazione con percorsi
     * @param dirName nome directory (CNF, E-CNF, etc.)
     * @param extension estensione file
     * @throws IOException se errori durante salvataggio
     */
    private static void saveFormulaToFile(String content, SolverConfiguration config,
                                          String dirName, String extension) throws IOException {
        System.out.println("Salvataggio della formula in " + dirName + "...");

        // Realizza la cartella di output
        Path outputDir = getOutputDirectory(config, dirName);
        Files.createDirectories(outputDir);

        String baseFileName = getBaseFileName(config.inputPath);
        Path outputFilePath = outputDir.resolve(baseFileName + extension);

        try (FileWriter writer = new FileWriter(outputFilePath.toFile())) {
            writer.write(content);
        }

        System.out.println("[I] Formula " + dirName + " salvata: " + outputFilePath);
    }

    /**
     * Salva le statistiche riguardo le opzioni aggiuntive all'interno della directory STATS
     *
     * @param statsContent contenuto statistiche
     * @param config configurazione con percorsi
     * @param optimizationType tipo di opzione (TSEITIN, SUBSUMPTION, RESTART)
     * @throws IOException se errori durante salvataggio
     */
    private static void saveOptimizationStats(String statsContent, SolverConfiguration config,
                                              String optimizationType) throws IOException {
        System.out.println("Salvataggio delle statistiche " + optimizationType + "...");

        Path statsDir = getOutputDirectory(config, "STATS").resolve(optimizationType);
        Files.createDirectories(statsDir);

        String baseFileName = getBaseFileName(config.inputPath);
        Path statsFilePath = statsDir.resolve(baseFileName + ".stats");

        try (FileWriter writer = new FileWriter(statsFilePath.toFile())) {
            writer.write(statsContent);
        }

        System.out.println("[I] Statistiche " + optimizationType + " salvate: " + statsFilePath);
    }

    /**
     * Salva file con le opzioni attive durante l'elaborazione.
     *
     * @param config configurazione con opzioni attive
     * @throws IOException se errori durante salvataggio
     */
    private static void saveActiveOptionsFile(SolverConfiguration config) throws IOException {
        List<String> activeOptions = buildActiveOptimizationsList(config);

        if (!activeOptions.isEmpty()) {
            Path statsDir = getOutputDirectory(config, "STATS");
            Files.createDirectories(statsDir);

            Path optionsFilePath = statsDir.resolve("opzioni_attive.txt");

            try (FileWriter writer = new FileWriter(optionsFilePath.toFile())) {
                writer.write("=== OPZIONI ATTIVE ===\n\n");

                if (config.useTseitin) {
                    writer.write("-> TSEITIN: Trasformazione in formula equisoddisfacibile E-CNF\n");
                }
                if (config.useSubsumption) {
                    writer.write("-> SUSSUNZIONE: Eliminazione clausole sovrainsieme\n");
                }
                if (config.useRestart) {
                    writer.write("-> RESTART: Reinizio periodico con sussunzione automatica\n");
                }
            }

            System.out.println("[I] File opzioni attive salvato: " + optionsFilePath);
        }
    }

    /**
     * Gestisce il risultato dell'elaborazione riuscita con l'output completo.
     *
     * Salva tutti i risultati finali (modello SAT o prova UNSAT) e
     * statistiche dettagliate, incluse quelle specifiche per restart.
     *
     * @param satResult risultato finale della risoluzione SAT
     * @param formulaResult metadata della pipeline di conversione
     * @param config configurazione utilizzata
     * @throws IOException se errori durante salvataggio
     */
    private static void handleSuccessfulResult(SATResult satResult, FormulaProcessingResult formulaResult,
                                               SolverConfiguration config) throws IOException {
        saveCompleteResults(satResult, formulaResult, config);
        displayFinalStatistics(satResult, formulaResult);

        // Salva statistiche restart se utilizzato
        if (config.useRestart && satResult.getStatistics().getRestarts() >= 0) {
            saveRestartStatistics(satResult, config);
        }
    }

    /**
     * Gestisce il caso di timeout durante la risoluzione SAT.
     *
     * Genera report specifico per indicare superamento limite temporale
     * con tutte le informazioni di configurazione utilizzate.
     *
     * @param config configurazione che ha causato timeout
     * @throws IOException se errori durante salvataggio report
     */
    private static void handleTimeoutResult(SolverConfiguration config) throws IOException {
        System.out.println("[W] Superato il timeout con limite di " + config.timeoutSeconds + " secondi");
        saveTimeoutReport(config);
    }

    /**
     * Gestisce gli errori durante l'elaborazione del file specifico.
     *
     * @param filePath percorso file che ha causato errore
     * @param e eccezione verificatasi
     */
    private static void handleFileProcessingError(String filePath, Exception e) {
        System.out.println("[E] Errore elaborazione del file '" + filePath + "': " + e.getMessage());
    }

    /**
     * Salva risultati SAT completi con modello o generazione della prova.
     *
     * @param satResult risultato completo della risoluzione
     * @param formulaResult metadata conversione formula
     * @param config configurazione utilizzata
     * @throws IOException se errori durante salvataggio
     */
    private static void saveCompleteResults(SATResult satResult, FormulaProcessingResult formulaResult,
                                            SolverConfiguration config) throws IOException {
        System.out.println("Salvataggio dei risultati...");

        Path resultDir = getOutputDirectory(config, "RESULT");
        Files.createDirectories(resultDir);

        String baseFileName = getBaseFileName(config.inputPath);
        Path resultFilePath = resultDir.resolve(baseFileName + ".result");

        try (FileWriter writer = new FileWriter(resultFilePath.toFile())) {
            writeStructuredResult(writer, satResult, formulaResult, config);
        }

        System.out.println("[I] Risultati salvati: " + resultFilePath);
    }

    /**
     * Scrive il risultato SAT strutturato nel file di output.
     *
     * @param writer writer per il file di output
     * @param satResult risultato SAT da scrivere
     * @param formulaResult metadata conversione
     * @param config configurazione utilizzata
     * @throws IOException se errori durante scrittura
     */
    private static void writeStructuredResult(FileWriter writer, SATResult satResult,
                                              FormulaProcessingResult formulaResult,
                                              SolverConfiguration config) throws IOException {
        // Header del report
        writer.write("=== RISOLUZIONE SAT ===\n");
        writer.write("File originale: " + Paths.get(config.inputPath).getFileName() + "\n");

        // Modalità specifica per convert (non genera file CNF)
        if (!config.isConvertMode) {
            writer.write("File CNF: " + getBaseFileName(config.inputPath) + ".cnf\n");
        } else {
            writer.write("Modalità: Conversione diretta CNF\n");
        }

        // Specifica se si sta eseguendo SAT sulla formula E-CNF oppure CNF
        if (config.useTseitin) {
            writer.write("File E-CNF: " + getBaseFileName(config.inputPath) + ".ecnf\n");
            writer.write("\nRisoluzione eseguita sulla formula E-CNF\n");
        } else {
            writer.write("\nRisoluzione eseguita sulla formula CNF\n");
        }

        // Opzioni utilizzate
        List<String> activeOpts = buildActiveOptimizationsList(config);
        if (!activeOpts.isEmpty()) {
            writer.write("Opzioni aggiuntive: " + String.join(", ", activeOpts) + "\n");
        }

        writer.write("\n" + "=".repeat(50) + "\n\n");

        // Contenuto principale
        if (satResult.isSatisfiable()) {
            writeSATResult(writer, satResult);
        } else {
            writeUNSATResult(writer, satResult);
        }

        // Statistiche finali
        writer.write("\n" + "=".repeat(50) + "\n\n");
        writeExecutionStatistics(writer, satResult, formulaResult);
    }

    /**
     * Genera l'output formattato per formule soddisfacibili (SAT)
     *
     * @param writer stream di scrittura verso file di output (già aperto e validato)
     * @param satResult risultato SAT contenente modello e metadata (garantito SAT)
     * @throws IOException se errori durante scrittura su file system
     */
    private static void writeSATResult(FileWriter writer, SATResult satResult) throws IOException {

        // Scrive L'intestazione risultato SAT
        writer.write("RISULTATO: SAT (soddisfacibile)\n\n");
        writer.write("Modello trovato:\n");

        // Verifica la presenza di un modello per la formula
        if (satResult.hasModel()) {

            // Ottiene la mappa completa variabile -> valore dal risultato SAT
            Map<String, Boolean> modelAssignments = satResult.getAssignment();

            // Ordina le variabili alfabeticamente per migliorare la leggibilità dell'output
            modelAssignments.entrySet().stream()
                    .sorted(Map.Entry.comparingByKey()) // Ordine alfabetico per chiave (nome variabile)
                    .forEach(variableAssignment -> {
                        try {
                            // FORMATO RIGA: "nomeVariabile = valorebooleano"
                            String variableName = variableAssignment.getKey();   // Es: "P", "Q", "R"
                            Boolean variableValue = variableAssignment.getValue(); // true/false

                            writer.write(variableName + " = " + variableValue + "\n");

                        } catch (IOException e) {
                            System.out.println("[E] Errore scrittura singola variabile modello: " + e.getMessage());
                        }
                    });

        } else {
            // Risultato SAT senza modello disponibile (non dovrebbe essere possibile)
            writer.write("Errore: modello non disponibile\n");
            System.out.println("[E] Inconsistenza: risultato SAT senza modello disponibile.");
        }
    }

    /**
     * Genera l'output formattato per formule insoddisfacibili (UNSAT)
     *
     * @param writer stream di scrittura verso file di output (già aperto e validato)
     * @param satResult risultato UNSAT contenente prova e metadata (garantito UNSAT)
     * @throws IOException se errori durante scrittura su file system
     */
    private static void writeUNSATResult(FileWriter writer, SATResult satResult) throws IOException {

        // Scrive L'intestazione risultato UNSAT
        writer.write("RISULTATO: UNSAT (insoddisfacibile)\n\n");

        // Verifica la presenza di una prova per la formula
        if (satResult.hasProof()) {
            writer.write("Prova di insoddisfacibilità:\n");

            // La prova è già formattata dal ProofGenerator:
            // <clausola di conflitto> ~ <clausola giustificante> => <clausola di spiegazione>
            String mathematicalProof = satResult.getProof();
            writer.write(mathematicalProof);

            // Controlla la presenza della clausola vuota finale
            boolean hasEmptyClauseInProof = mathematicalProof.toLowerCase().contains("[]");

            if (!hasEmptyClauseInProof) {
                writer.write("\n\nLa clausola vuota [] conclude la dimostrazione.\n");

                // Segnala che la prova è potenzialmente incompleta
                System.out.println("[W] Prova UNSAT senza clausola vuota esplicita nel testo finale");
            }

        } else {
            // Risultato UNSAT senza prova disponibile
            // Può verificarsi in caso di:
            // - Timeout durante generazione prova
            // - Errori nel ProofGenerator
            // - Interruzione prematura dell'algoritmo
            writer.write("Prova non disponibile.\n");

            System.out.println("[W] Risultato UNSAT generato senza prova matematica disponibile");
        }
    }

    /**
     * Genera il report riguardo le prestazioni dell'algoritmo CDCL
     *
     * Scrive nel file di output le metriche dettagliate di performance raccolte durante
     * l'esecuzione dell'algoritmo CDCL, fornendo informazioni sulla complessità del problema
     * e sull'efficacia delle euristiche utilizzate.
     *
     * METRICHE INCLUSE:
     * - Decisioni: Scelte euristiche VSIDS effettuate durante la ricerca
     * - Propagazioni: Implicazioni unitarie derivate automaticamente (solo per SAT)
     * - Conflitti: Conflitti rilevati e analizzati per l'apprendimento
     * - Clausole apprese: Nuove clausole generate tramite l'analisi dei conflitti
     * - Restart: Operazioni di reinizio per prevenzione stalli (se utilizzate)
     * - Tempo: Durata totale esecuzione in millisecondi
     *
     * DIFFERENZIAZIONE TRA SAT e UNSAT:
     * - SAT: Include tutte le informazioni: decisioni, propagazioni, conflitti, ...
     * - UNSAT: Solo conflitti e apprendimento
     *
     * @param writer stream di scrittura verso file di output (già aperto e validato)
     * @param satResult risultato completo contenente statistiche di esecuzione
     * @throws IOException se errori durante scrittura su file system
     */
    private static void writeExecutionStatistics(FileWriter writer, SATResult satResult, FormulaProcessingResult formulaResult) throws IOException {
        // Estrae tutte le metriche raccolte durante CDCL
        var stats = satResult.getStatistics();

        // Calcola le statistiche totali senza considerare quelle dovute alle
        // clausole unitarie assunte vere prima della prima decisione
        int totalPropagations = 0;
        int totalConflicts = 0;
        int totalExplanations = 0;
        int totalLearnedClauses = 0;

        if (stats.hasDecisionBreakdown()) {
            List<SATStatistics.DecisionBreakdown> breakdowns = stats.getDecisionBreakdowns();

            // Somma tutte le statistiche per decisione
            for (SATStatistics.DecisionBreakdown breakdown : breakdowns) {
                totalPropagations += breakdown.propagations;
                totalConflicts += breakdown.conflicts;
                totalExplanations += breakdown.explanations;
                totalLearnedClauses += breakdown.learnedClauses;
            }
        }

        // STATISTICHE TOTALI
        writer.write("\n=== STATISTICHE TOTALI ===\n");
        writer.write("Clausole iniziali: " + formulaResult.initialClausesCount() + "\n");
        writer.write("Variabili iniziali: " + formulaResult.initialVariablesCount() + "\n");
        writer.write("Decisioni totali: " + stats.getDecisions() + "\n");
        writer.write("Propagazioni totali: " + stats.getPropagations() + "\n");
        writer.write("Conflitti totali: " + stats.getConflicts() + "\n");
        writer.write("Spiegazioni totali: " + stats.getExplanations() + "\n");
        writer.write("Clausole apprese totali: " + stats.getLearnedClauses() + "\n");

        // Reinizio (opzionale)
        if (stats.getRestarts() >= 0) {
            // Restart eseguiti
            writer.write("Reinizio: " + stats.getRestarts() + "\n");
        }

        // Include parsing, conversione CNF, risoluzione CDCL, generazione output
        writer.write("Tempo impiegato: " + stats.getExecutionTimeMs() + " ms\n");

        // Si riportano le statistiche specifiche per ogni decisione
        if (stats.hasDecisionBreakdown() || true) {
            writer.write("\n=== STATISTICHE PER DECISIONE ===\n");

            writer.write(String.format("- PRE #1-decisione: %d propagazioni, %d conflitti, %d spiegazioni, %d clausole apprese\n",
                    stats.getPropagations() - totalPropagations,
                    stats.getConflicts() - totalConflicts,
                    stats.getExplanations() - totalExplanations,
                    stats.getLearnedClauses() - totalLearnedClauses));

            List<SATStatistics.DecisionBreakdown> breakdowns = stats.getDecisionBreakdowns();

            for (SATStatistics.DecisionBreakdown breakdown : breakdowns) {
                writer.write(String.format("- Decisione #%d: %d propagazioni, %d conflitti, %d spiegazioni, %d clausole apprese\n",
                        breakdown.decisionNumber,
                        breakdown.propagations,
                        breakdown.conflicts,
                        breakdown.explanations,
                        breakdown.learnedClauses));
            }
        } else {
            writer.write("\n=== STATISTICHE PER DECISIONE ===\n");
            writer.write("Non è servito fare nemmeno una decisione.");
        }
    }

    /**
     * Genera il report dettagliato della tecnica reinizio
     *
     * Crea un file di report specifico per analizzare l'utilizzo e l'efficacia della
     * tecnica restart durante la risoluzione CDCL. Le statistiche vengono salvate in
     * una sottodirectory dedicata per facilitare l'analisi delle performance.
     *
     * CONTENUTO REPORT GENERATO:
     * - Numero restart eseguiti vs soglia configurata (5 conflitti)
     * - Conflitti totali rilevati durante l'intera esecuzione
     * - Media conflitti per restart (efficacia della strategia)
     * - Valutazione qualitativa dell'uso della tecnica
     *
     * STRUTTURA FILE OUTPUT:
     * STATS/RESTART/nomeFile.stats - Report dedicato restart per questo problema
     *
     * @param result risultato SAT completo con statistiche di esecuzione
     * @param config configurazione solver contenente percorsi input/output
     * @throws IOException se errori durante creazione directory o scrittura file
     */
    private static void saveRestartStatistics(SATResult result, SolverConfiguration config) throws IOException {
        System.out.println("Salvataggio statistiche restart...");

        // Crea la directory STATS/RESTART/
        Path restartStatsDir = getOutputDirectory(config, "STATS").resolve("RESTART");
        Files.createDirectories(restartStatsDir);

        String baseFileName = getBaseFileName(config.inputPath);
        Path statsFilePath = restartStatsDir.resolve(baseFileName + ".stats");

        try (FileWriter writer = new FileWriter(statsFilePath.toFile())) {
            // Header del report
            writer.write("=== STATISTICHE RESTART ===\n\n");

            // Ottiene le statistiche complete dall'esecuzione CDCL
            var stats = result.getStatistics();

            // Informazioni sulla tecnica di reinizio
            writer.write("Reinizio eseguiti: " + stats.getRestarts() + "\n");
            writer.write("Conflitti totali: " + stats.getConflicts() + "\n");
            writer.write("Soglia reinizio: 5 conflitti\n"); // Configurazione fissa dell'algoritmo

            // Si valuta l'efficacia basata sui dati raccolti
            if (stats.getRestarts() > 0) {
                // Media dei conflitti per reinizio indica la frequenza di utilizzo
                double avgConflicts = (double) stats.getConflicts() / stats.getRestarts();
                writer.write("Media conflitti/restart: " + String.format("%.1f", avgConflicts) + "\n");

                // Reinizio utilizzati attivamente
                writer.write("\nEfficacia: Restart utilizzati per prevenire stalli\n");
            } else {
                // Nessun reinizio necessario (risoluzione efficiente)
                writer.write("\nNessun restart necessario - risoluzione lineare\n");
            }
        }

        System.out.println("Statistiche restart salvate: " + statsFilePath);
    }

    /**
     * Genera la documentazione per le esecuzioni interrotte
     *
     * Crea un file di report standardizzato quando il solutore CDCL viene interrotto
     * per il superamento del limite temporale configurato.
     *
     * UTILIZZO:
     * Chiamato quando ExecutorService.get() lancia un TimeoutException nel solver principale
     *
     * @param config configurazione solver con percorsi, timeout e ottimizzazioni attive
     * @throws IOException se errori durante creazione directory o scrittura file
     */
    private static void saveTimeoutReport(SolverConfiguration config) throws IOException {
        // Usa directory RESULT per coerenza con gli altri esiti
        Path resultDir = getOutputDirectory(config, "RESULT");
        Files.createDirectories(resultDir); // Assicura esistenza directory di output

        // Mantiene correlazione con file input originale
        String baseFileName = getBaseFileName(config.inputPath);
        Path resultFilePath = resultDir.resolve(baseFileName + ".result");

        try (FileWriter writer = new FileWriter(resultFilePath.toFile())) {
            writer.write("=== RISOLUZIONE SAT ===\n");

            // Tracciabilità del file che ha causato il timeout
            writer.write("File originale: " + Paths.get(config.inputPath).getFileName() + "\n");

            // Timeout configurato che ha determinato l'interruzione
            writer.write("Timeout: " + config.timeoutSeconds + " secondi\n\n");

            // Serve per capire se il timeout è dovuto alle opzioni facoltative aggiuntive
            List<String> activeOpts = buildActiveOptimizationsList(config);
            if (!activeOpts.isEmpty()) {
                writer.write("Opzioni aggiuntive: " + String.join(", ", activeOpts) + "\n");
            }

            writer.write("\n" + "=".repeat(50) + "\n\n");
            writer.write("RISULTATO: TIMEOUT\n");
            writer.write("La risoluzione ha superato il limite di tempo.\n\n");

            // Guida l'utente verso possibili soluzioni
            writer.write("Aumentare il timeout (-t) per problemi complessi.\n");
        }
    }

    /**
     * Mostra all'utente un riepilogo immediato e leggibile dei risultati dell'elaborazione
     * SAT appena completata.
     *
     * @param result risultato SAT completo con esito e statistiche di esecuzione
     * @param formulaResult metadata della pipeline di conversione formula (attualmente non utilizzato)
     */
    private static void displayFinalStatistics(SATResult result, FormulaProcessingResult formulaResult) {
        System.out.println("Elaborazione completata!\n");

        // Converte risultato booleano in stringa
        String resultStr = result.isSatisfiable() ? "SAT" : "UNSAT";

        // Ottiene metriche performance dall'esecuzione CDCL
        var stats = result.getStatistics();

        // Riepilogo delle statistiche
        System.out.println(">>> RISULTATO FINALE <<<");
        System.out.println("Esito: " + resultStr);
        System.out.println("Decisioni: " + stats.getDecisions());
        System.out.println("Conflitti: " + stats.getConflicts());
        // Solo se presenti
        if (stats.getRestarts() > 0) {
            System.out.println("Restart: " + stats.getRestarts());
        }
        System.out.println("Tempo: " + stats.getExecutionTimeMs() + " ms");
        System.out.println("========================\n");
    }

    //endregion

    //region GESTIONE DEI PERCORSI

    /**
     * Ottiene le directory di output basata sulla configurazione.
     *
     * @param config configurazione con percorsi
     * @param subdirName nome sottodirectory (CNF, RESULT, etc.)
     * @return percorso directory di output
     */
    private static Path getOutputDirectory(SolverConfiguration config, String subdirName) {
        if (config.outputPath != null) {
            return Paths.get(config.outputPath).resolve(subdirName);
        } else {
            Path parentDir = Paths.get(config.inputPath).getParent();
            return parentDir != null ? parentDir.resolve(subdirName) : Paths.get(subdirName);
        }
    }

    /**
     * Estrae nome base del file senza estensione.
     *
     * @param filePath percorso file completo
     * @return nome file senza estensione
     */
    private static String getBaseFileName(String filePath) {
        String fileName = Paths.get(filePath).getFileName().toString();
        int lastDot = fileName.lastIndexOf('.');
        return lastDot > 0 ? fileName.substring(0, lastDot) : fileName;
    }

    /**
     * Crea configurazione specifica per un file nel batch.
     *
     * @param file file da elaborare
     * @param baseConfig configurazione base del batch
     * @return configurazione specifica per il file
     */
    private static SolverConfiguration createFileConfiguration(File file, SolverConfiguration baseConfig) {
        return new SolverConfiguration(
                file.getAbsolutePath(),
                baseConfig.outputPath,
                true, // modalità file
                baseConfig.timeoutSeconds,
                baseConfig.useTseitin,
                baseConfig.useSubsumption,
                baseConfig.useRestart,
                false, // non modalità generazione
                null,  // nessun tipo generazione
                0,     // nessun conteggio generazione
                false  // non modalità convert
        );
    }

    /**
     * Crea configurazione specifica per un file CNF nel batch convert.
     *
     * @param file file da elaborare
     * @param baseConfig configurazione base del batch
     * @return configurazione specifica per il file con modalità convert
     */
    private static SolverConfiguration createConvertFileConfiguration(File file, SolverConfiguration baseConfig) {
        return new SolverConfiguration(
                file.getAbsolutePath(),
                baseConfig.outputPath,
                true, // modalità file
                baseConfig.timeoutSeconds,
                baseConfig.useTseitin,
                baseConfig.useSubsumption,
                baseConfig.useRestart,
                false, // non modalità generazione
                null,  // nessun tipo generazione
                0,     // nessun conteggio generazione
                true   // modalità convert
        );
    }

    //endregion

    //region HELP E DOCUMENTAZIONE

    /**
     * Visualizza l'help completo dell'applicazione.
     *
     * Mostra tutti i parametri supportati, esempi di utilizzo e note operative
     * per guidare l'utente nell'uso corretto del solutore SAT.
     */
    private static void printApplicationHelp() {
        System.out.println("\n::>> SOLUTORE SAT CDCL <<::");
        System.out.println("Solutore avanzato per problemi di soddisfacibilità booleana (SAT)");
        System.out.println("con algoritmo CDCL e ottimizzazioni state-of-the-art\n");

        System.out.println("UTILIZZO:");
        System.out.println("  java -jar solutore_SAT.jar [opzioni]\n");

        System.out.println("MODALITÀ OPERATIVE:");
        System.out.println("  1. RISOLUZIONE SAT:");
        System.out.println("     -f <file>       Elabora un singolo file .txt");
        System.out.println("     -d <directory>  Elabora tutti i file .txt in una directory");
        System.out.println("     -o <directory>  Directory di output (default: stessa di input)");
        System.out.println("     -t <secondi>    Timeout per formula (min: 5, default: 10)");
        System.out.println("     -opt=<flags>    Ottimizzazioni (s=sussunzione, t=tseitin, r=restart, all=tutte)");
        System.out.println();
        System.out.println("  2. CONVERSIONE DIRETTA CNF:");
        System.out.println("     -f <file.cnf> -convert    Elabora un singolo file .cnf in formato standard");
        System.out.println("     -d <directory> -convert   Elabora tutti i file .cnf in una directory");
        System.out.println("     -o <directory>            Directory output per risultati");
        System.out.println("     -t <secondi>              Timeout per formula");
        System.out.println("     -opt=<flags>              Ottimizzazioni (s=sussunzione, t=tseitin, r=restart)");
        System.out.println();
        System.out.println("  3. GENERAZIONE ISTANZE:");
        System.out.println("     -gen=pigeonhole <numero>  Genera istanze Pigeonhole Problem (1-100)");
        System.out.println("     -o <directory>           Directory output per istanze generate");
        System.out.println();
        System.out.println("  4. AIUTO:");
        System.out.println("     -h              Mostra questa guida\n");

        System.out.println("OTTIMIZZAZIONI DISPONIBILI (-opt=<flags>):");
        System.out.println("  s = Sussunzione      (elimina clausole ridondanti)");
        System.out.println("  t = Tseitin         (conversione E-CNF per formule complesse)");
        System.out.println("  r = Restart         (reinizio periodico con sussunzione)");
        System.out.println("  all = Tutte le ottimizzazioni disponibili\n");

        System.out.println("FORMATO CNF STANDARD (-convert):");
        System.out.println("  Ogni riga: <letterali separati da spazi> 0");
        System.out.println("  Letterali positivi: numeri positivi (1, 2, 3, ...)");
        System.out.println("  Letterali negativi: numeri negativi (-1, -2, -3, ...)");
        System.out.println("  Terminatore riga: 0");
        System.out.println("  Righe di commento/header: ignorate automaticamente\n");

        System.out.println("ESEMPI DI UTILIZZO:");
        System.out.println("  # Risoluzione SAT - File singolo base");
        System.out.println("  java -jar solutore_SAT.jar -f formula.txt\n");

        System.out.println("  # Risoluzione SAT - Con opzioni aggiuntive restart e sussunzione");
        System.out.println("  java -jar solutore_SAT.jar -f formula.txt -opt=sr\n");

        System.out.println("  # Risoluzione SAT - Directory con tutte le opzioni aggiuntive");
        System.out.println("  java -jar solutore_SAT.jar -d ./problemi/ -opt=all -t 60\n");

        System.out.println("  # Conversione diretta CNF - File singolo");
        System.out.println("  java -jar solutore_SAT.jar -f problema.cnf -convert\n");

        System.out.println("  # Conversione diretta CNF - Directory con ottimizzazioni");
        System.out.println("  java -jar solutore_SAT.jar -d ./cnf_files/ -convert -opt=sr -t 30\n");

        System.out.println("  # Generazione istanze Pigeonhole Problem");
        System.out.println("  java -jar solutore_SAT.jar -gen=pigeonhole 15 -o ./output/\n");

        System.out.println("  # Risoluzione SAT - Output personalizzato");
        System.out.println("  java -jar solutore_SAT.jar -d ./input/ -o ./output/ -opt=t\n");

        System.out.println("OUTPUT GENERATO:");
        System.out.println("  CNF/          Formula convertite in Forma Normale Congiuntiva (non in modalità -convert)");
        System.out.println("  E-CNF/        Formula Tseitin equisoddisfacibili (con -opt=t)");
        System.out.println("  RESULT/       Risultati SAT/UNSAT con modelli e prove");
        System.out.println("  STATS/        Statistiche dettagliate per tipo ottimizzazione");
        System.out.println("  PIGEONHOLE/   Istanze generate del Pigeonhole Problem\n");

        System.out.println("NOTE OPERATIVE:");
        System.out.println("  - Formule .txt: AND(&), OR(|), NOT(!), IMPLIES(->), IFF(<->)");
        System.out.println("  - File .cnf: Formato DIMACS standard con terminatori 0");
        System.out.println("  - Modalità -convert: Solo file .cnf, genera variabili p1, p2, ...");
        System.out.println("  - Le modalità risoluzione SAT e generazione istanze sono mutualmente esclusive");
        System.out.println("  - Tseitin raccomandato per formule con >8 operatori");
        System.out.println("  - Restart efficace su problemi con pattern di stallo");
        System.out.println("  - Timeout minimo 5s per evitare interruzioni premature");
        System.out.println("  - Batch elabora automaticamente tutti i file della directory");
        System.out.println("  - Pigeonhole Problem genera istanze UNSAT per testing\n");

        System.out.println("===============================================\n");
    }

    //endregion

    //region CLASSI DI SUPPORTO E CONFIGURAZIONE

    /**
     * Configurazione validata dell'applicazione.
     *
     * Contiene tutti i parametri di esecuzione in forma immutabile
     * per garantire consistenza durante l'elaborazione.
     */
    private static class SolverConfiguration {
        final String inputPath;
        final String outputPath;
        final boolean isFileMode;
        final int timeoutSeconds;
        final boolean useTseitin;
        final boolean useSubsumption;
        final boolean useRestart;
        final boolean isGenerationMode;
        final String generationType;
        final int generationCount;
        final boolean isConvertMode;

        SolverConfiguration(String inputPath, String outputPath, boolean isFileMode,
                            int timeoutSeconds, boolean useTseitin, boolean useSubsumption, boolean useRestart,
                            boolean isGenerationMode, String generationType, int generationCount,
                            boolean isConvertMode) {
            this.inputPath = inputPath;
            this.outputPath = outputPath;
            this.isFileMode = isFileMode;
            this.timeoutSeconds = timeoutSeconds;
            this.useTseitin = useTseitin;
            this.useSubsumption = useSubsumption;
            this.useRestart = useRestart;
            this.isGenerationMode = isGenerationMode;
            this.generationType = generationType;
            this.generationCount = generationCount;
            this.isConvertMode = isConvertMode;
        }
    }

    /**
     * Parser robusto per parametri linea di comando.
     *
     * Gestisce validazione completa di tutti i parametri con
     * messaggi di errore informativi per l'utente.
     */
    private static class ArgumentParser {

        /**
         * Processa sequenzialmente tutti i parametri della command line, validando sintassi e
         * semantica, e costruisce un oggetto SolverConfiguration completo e validato.
         *
         * PARAMETRI SUPPORTATI:
         * -h: Mostra help e termina
         * -f <file>: Input file singolo (esclusivo con -d e -gen)
         * -d <dir>: Input directory per batch (esclusivo con -f e -gen)
         * -gen=<tipo> <numero>: Generazione istanze (esclusivo con -f e -d)
         * -o <dir>: Directory output personalizzata
         * -t <sec>: Timeout in secondi per singola risoluzione
         * -opt=<flags>: Ottimizzazioni (t=Tseitin, s=Subsumption, r=Restart)
         * -convert: Modalità conversione diretta CNF (richiede -f o -d)
         *
         * @param args parametri da linea comando forniti dall'utente
         * @return configurazione solver validata e pronta per l'uso (null se help richiesto)
         * @throws IllegalArgumentException se parametri sintatticamente o semanticamente invalidi
         */
        public SolverConfiguration parse(String[] args) {
            // Variabili per raccogliere parametri durante parsing
            String inputPath = null;
            String outputPath = null;
            boolean isFileMode = false;                     // Flag per modalità file singolo (-f)
            boolean isDirectoryMode = false;                // Flag per modalità directory (-d)
            boolean isGenerationMode = false;               // Flag per modalità generazione (-gen)
            boolean isConvertMode = false;                  // Flag per modalità conversione (-convert)
            boolean useTseitin = false;                     // Opzione di conversione in E-CNF via Tseitin
            boolean useSubsumption = false;                 // Opzione di eliminazione clausole soprainsieme
            boolean useRestart = false;                     // Opzione di reinizio
            String generationType = null;                   // Tipo di generazione (pigeonhole, ...)
            int generationCount = 0;                        // Numero istanze da generare
            int timeoutSeconds = DEFAULT_TIMEOUT_SECONDS;   // Timeout default se non specificato

            // Processa sequenzialmente ogni argomento della command line
            for (int i = 0; i < args.length; i++) {
                switch (args[i]) {
                    // Mostra documentazione e termina senza configurazione
                    case HELP_PARAM -> {
                        printApplicationHelp();
                        return null; // Segnala al chiamante di terminare
                    }

                    // Input da file singolo (mutualmente esclusivo con directory e generazione)
                    case FILE_PARAM -> {
                        validateExclusiveMode(isDirectoryMode, isGenerationMode, "file");
                        inputPath = getNextArgument(args, ++i, "file");
                        validateFileExists(inputPath);
                        isFileMode = true;
                    }

                    // Input da directory per batch processing
                    case DIR_PARAM -> {
                        validateExclusiveMode(isFileMode, isGenerationMode, "directory");
                        inputPath = getNextArgument(args, ++i, "directory");
                        validateDirectoryExists(inputPath);
                        isDirectoryMode = true;
                    }

                    // Specifica la directory personalizzata per i risultati
                    case OUTPUT_PARAM -> {
                        outputPath = getNextArgument(args, ++i, "directory output");
                        validateOrCreateOutputDirectory(outputPath);
                    }

                    // Imposta limite temporale per risoluzione
                    case TIMEOUT_PARAM -> {
                        timeoutSeconds = parseAndValidateTimeout(args, ++i);
                    }

                    // Modalità conversione diretta CNF
                    case CONVERT_PARAM -> {
                        isConvertMode = true;
                    }

                    // Opzioni aggiuntive e parametri sconosciuti
                    default -> {
                        // Parsing parametri -opt con flags multiple
                        if (args[i].startsWith(OPT_PARAM)) {
                            String optValue = args[i].substring(OPT_PARAM.length());
                            OptimizationFlags flags = parseOptionalFlags(optValue);
                            useTseitin = flags.tseitin;
                            useSubsumption = flags.subsumption;
                            useRestart = flags.restart;
                        }
                        // Parsing parametri -gen per generazione istanze
                        else if (args[i].startsWith(GEN_PARAM)) {
                            validateExclusiveMode(isFileMode, isDirectoryMode, "generazione");
                            GenerationConfig genConfig = parseGenerationParameters(args, i);
                            generationType = genConfig.type;
                            generationCount = genConfig.count;
                            isGenerationMode = true;
                            i = genConfig.nextIndex; // Salta parametri consumati
                        }
                        else {
                            throw new IllegalArgumentException("Parametro sconosciuto: " + args[i]);
                        }
                    }
                }
            }

            // Validazione finale configurazione
            return validateAndBuildFinalConfiguration(inputPath, outputPath, isFileMode, isDirectoryMode,
                    isGenerationMode, isConvertMode, timeoutSeconds, useTseitin, useSubsumption, useRestart,
                    generationType, generationCount);
        }

        /**
         * Valida che le modalità operative siano mutualmente esclusive.
         */
        private void validateExclusiveMode(boolean mode1, boolean mode2, String currentMode) {
            if (mode1 || mode2) {
                throw new IllegalArgumentException("Modalità " + currentMode +
                        " non può essere combinata con altre modalità (file/directory/generazione sono mutualmente esclusive)");
            }
        }

        /**
         * Parsa parametri per generazione istanze.
         */
        private GenerationConfig parseGenerationParameters(String[] args, int currentIndex) {
            String genParam = args[currentIndex];
            String genType = genParam.substring(GEN_PARAM.length());

            // Valida tipo generazione
            if (!GEN_PIGEONHOLE.equals(genType)) {
                throw new IllegalArgumentException("Tipo generazione non supportato: " + genType +
                        ". Supportati: " + GEN_PIGEONHOLE);
            }

            // Ottiene numero istanze
            if (currentIndex + 1 >= args.length) {
                throw new IllegalArgumentException("Parametro -gen=" + genType + " richiede numero istanze");
            }

            int count;
            try {
                count = Integer.parseInt(args[currentIndex + 1]);
            } catch (NumberFormatException e) {
                throw new IllegalArgumentException("Numero istanze non valido: " + args[currentIndex + 1]);
            }

            // Valida range numero istanze
            if (count < MIN_PIGEONHOLE_INSTANCES || count > MAX_PIGEONHOLE_INSTANCES) {
                throw new IllegalArgumentException("Numero istanze deve essere tra " +
                        MIN_PIGEONHOLE_INSTANCES + " e " + MAX_PIGEONHOLE_INSTANCES + ", ricevuto: " + count);
            }

            return new GenerationConfig(genType, count, currentIndex + 1);
        }

        /**
         * Valida configurazione finale e costruisce oggetto risultato.
         */
        private SolverConfiguration validateAndBuildFinalConfiguration(String inputPath, String outputPath,
                                                                       boolean isFileMode, boolean isDirectoryMode, boolean isGenerationMode, boolean isConvertMode,
                                                                       int timeoutSeconds, boolean useTseitin, boolean useSubsumption, boolean useRestart,
                                                                       String generationType, int generationCount) {

            // Per modalità generazione, inputPath e timeout non sono necessari
            if (isGenerationMode) {
                if (outputPath == null) {
                    throw new IllegalArgumentException("Modalità generazione richiede directory output (-o)");
                }
                return new SolverConfiguration(null, outputPath, false, 0, false, false, false,
                        true, generationType, generationCount, false);
            }

            // Per modalità convert, valida che sia specificato input
            if (isConvertMode) {
                if (inputPath == null) {
                    throw new IllegalArgumentException("Modalità -convert richiede input con -f (file) o -d (directory)");
                }

                // Valida estensione .cnf per modalità convert
                if (isFileMode && !inputPath.toLowerCase().endsWith(".cnf")) {
                    throw new IllegalArgumentException("Modalità -convert richiede file con estensione .cnf");
                }

                return new SolverConfiguration(inputPath, outputPath, isFileMode, timeoutSeconds,
                        useTseitin, useSubsumption, useRestart, false, null, 0, true);
            }

            // Per modalità risoluzione SAT normale, inputPath è obbligatorio
            if (inputPath == null) {
                throw new IllegalArgumentException("Specificare input con -f (file) o -d (directory)");
            }

            return new SolverConfiguration(inputPath, outputPath, isFileMode, timeoutSeconds,
                    useTseitin, useSubsumption, useRestart, false, null, 0, false);
        }

        /**
         * Verifica che esista effettivamente un argomento successivo nell'array prima
         * di restituirlo, prevenendo IndexOutOfBoundsException durante il parsing.
         */
        private String getNextArgument(String[] args, int currentIndex, String argumentType) {
            if (currentIndex >= args.length) {
                throw new IllegalArgumentException("Parametro " + args[currentIndex - 1] +
                        " richiede " + argumentType);
            }
            return args[currentIndex];
        }

        /**
         * Estrae il valore del timeout dalla command line, lo converte da stringa a intero
         * e applica validazioni di range per garantire un valore utilizzabile dal solver.
         */
        private int parseAndValidateTimeout(String[] args, int currentIndex) {
            String timeoutStr = getNextArgument(args, currentIndex, "numero secondi");

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
         * Analizza la stringa di flags passata al parametro -opt e converte ogni carattere
         * in una configurazione booleana specifica per le opzioni aggiuntive del solver CDCL.
         */
        private OptimizationFlags parseOptionalFlags(String flagsStr) {
            if (flagsStr == null || flagsStr.trim().isEmpty()) {
                throw new IllegalArgumentException("Valore -opt vuoto");
            }

            if (flagsStr.equals(OPT_ALL)) {
                return new OptimizationFlags(true, true, true);
            }

            boolean tseitin = flagsStr.contains(OPT_TSEITIN);
            boolean subsumption = flagsStr.contains(OPT_SUBSUMPTION);
            boolean restart = flagsStr.contains(OPT_RESTART);

            return new OptimizationFlags(tseitin, subsumption, restart);
        }

        /**
         * Esegue i controlli completi su un file specificato dall'utente per garantire che
         * il solver possa accedervi e processarlo.
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

        private void validateOrCreateOutputDirectory(String dirPath) {
            File dir = new File(dirPath);
            if (!dir.exists()) {
                System.out.println("Creazione directory output: " + dirPath);
                if (!dir.mkdirs()) {
                    throw new IllegalArgumentException("Impossibile creare directory: " + dirPath);
                }
            } else if (!dir.isDirectory()) {
                throw new IllegalArgumentException("Percorso non è una directory: " + dirPath);
            }
            if (!dir.canWrite()) {
                throw new IllegalArgumentException("Directory non scrivibile: " + dirPath);
            }
        }
    }

    /**
     * Flag di ottimizzazione parsed dalla linea di comando.
     */
    private record OptimizationFlags(boolean tseitin, boolean subsumption, boolean restart) {}

    /**
     * Configurazione per generazione istanze.
     */
    private record GenerationConfig(String type, int count, int nextIndex) {}

    /**
     * Risultato elaborazione batch con statistiche.
     */
    private static class BatchResult {
        final int totalFiles;
        int successCount = 0;
        int errorCount = 0;

        BatchResult(int totalFiles) {
            this.totalFiles = totalFiles;
        }

        void incrementSuccess() { successCount++; }
        void incrementError() { errorCount++; }
    }

    /**
     * Risultato conversione CNF con formula e stringa.
     */
    private record CNFConversionResult(CNFConverter cnfFormula, String cnfString) {}

    /**
     * Risultato conversione Tseitin completa.
     */
    private record TseitinConversionResult(CNFConverter ecnfFormula, String ecnfString, String conversionInfo) {}

    /**
     * Risultato ottimizzazione sussunzione.
     */
    private record SubsumptionResult(CNFConverter optimizedFormula, String optimizationInfo) {}

    /**
     * Risultato completo processamento formula.
     */
    private record FormulaProcessingResult(CNFConverter finalFormula, String conversionInfo, boolean isECNF,
                                           int initialClausesCount, int initialVariablesCount) {}

    //endregion
}