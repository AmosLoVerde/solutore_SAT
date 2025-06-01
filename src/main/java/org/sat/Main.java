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

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;
import java.util.stream.Stream;
import java.util.concurrent.*;

/**
 * Classe principale per l'avvio del solutore SAT CDCL.
 *
 * Questo software implementa un solutore SAT (Boolean Satisfiability) utilizzando
 * l'algoritmo CDCL (Conflict-Driven Clause Learning) con le seguenti caratteristiche:
 *   - Euristica VSIDS (Variable State Independent Decaying Sum) per la decisione
 *   - First 1UIP (First Unique Implication Point) per l'apprendimento delle clausole e salto all'indietro
 *   - Generazione automatica di prove di insoddisfacibilità
 *
 * Opzioni extra:
 *   - Gestione timeout per evitare computazioni infinite
 *   - Supporto per elaborazione di file singoli o directory
 *
 * Il solutore accetta formule logiche in formato testuale e le converte automaticamente
 * in forma normale congiuntiva (CNF) prima di applicare l'algoritmo CDCL.
 *
 * @author Amos Lo Verde
 * @version 1.5.0
 */
public final class Main {
    /**
     * Logger per la registrazione dei messaggi di sistema
     */
    private static final Logger LOGGER = Logger.getLogger(Main.class.getName());

    /**
     * Parametri della linea di comando supportati
     */
    private static final String HELP_PARAM = "-h";           // Mostra la guida
    private static final String FILE_PARAM = "-f";           // Specifica un file singolo
    private static final String DIR_PARAM = "-d";            // Specifica una directory
    private static final String OUTPUT_PARAM = "-o";         // Directory di output personalizzata
    private static final String TIMEOUT_PARAM = "-t";        // Timeout in secondi

    /**
     * Configurazioni di timeout
     */
    private static final int DEFAULT_TIMEOUT_SECONDS = 10;   // Timeout predefinito
    private static final int MIN_TIMEOUT_SECONDS = 5;        // Timeout minimo consentito

    /**
     * Costruttore privato per prevenire l'istanziazione.
     * Questa è una classe utility che contiene solo metodi statici.
     */
    private Main() {
        throw new UnsupportedOperationException("Classe utility - non istanziabile");
    }


    /**
     * Punto di ingresso principale dell'applicazione.
     *
     * Gestisce l'analisi dei parametri della linea di comando e avvia il processo
     * di risoluzione appropriato (file singolo o directory).
     *
     * @param args argomenti dalla linea di comando
     * @throws RuntimeException se si verificano errori critici durante l'elaborazione
     */
    public static void main(String[] args) {
        LOGGER.info("=== AVVIO SOLUTORE SAT CDCL ===");

        try {
            // Verifica la presenza di parametri
            if (args.length == 0) {
                displayNoParametersMessage();
                return;
            }

            // Analizza i parametri della linea di comando
            CommandLineResult cmdResult = parseCommandLineArguments(args);
            if (cmdResult == null) {
                return; // Errore già gestito o help mostrato
            }

            // Mostra configurazione
            displayConfiguration(cmdResult);

            // Avvia l'elaborazione in base alla modalità
            executeProcessingMode(cmdResult);

        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Errore critico nell'applicazione", e);
            System.err.println("ERRORE CRITICO: " + e.getMessage());
            System.exit(1);
        } finally {
            LOGGER.info("=== FINE ESECUZIONE SOLUTORE SAT ===");
        }
    }


    /**
     * Mostra il messaggio quando non sono forniti parametri.
     */
    private static void displayNoParametersMessage() {
        String message = "Nessun parametro fornito. Usa -h per visualizzare l'help.";
        LOGGER.info(message);
        System.out.println(message);
    }

    /**
     * Mostra la configurazione corrente.
     *
     * @param config configurazione analizzata dalla linea di comando
     */
    private static void displayConfiguration(CommandLineResult config) {
        System.out.println("\n=== CONFIGURAZIONE SOLUTORE SAT ===");
        System.out.println("Timeout configurato: " + config.getTimeoutSeconds() + " secondi");

        if (config.isFileMode()) {
            System.out.println("Modalità: File singolo");
            System.out.println("File di input: " + config.getPath());
        } else if (config.isDirectoryMode()) {
            System.out.println("Modalità: Directory");
            System.out.println("Directory di input: " + config.getPath());
        }

        if (config.getOutputPath() != null) {
            System.out.println("Directory di output: " + config.getOutputPath());
        } else {
            System.out.println("Directory di output: Default (nella stessa cartella dell'input)");
        }
        System.out.println("====================================\n");
    }

    /**
     * Esegue l'elaborazione in base alla modalità selezionata.
     *
     * @param config configurazione dell'elaborazione
     */
    private static void executeProcessingMode(CommandLineResult config) {
        if (config.isFileMode()) {
            LOGGER.info("Modalità file singolo - Input: " + config.getPath());
            processFile(config.getPath(), config.getOutputPath(), config.getTimeoutSeconds());

        } else if (config.isDirectoryMode()) {
            LOGGER.info("Modalità directory - Input: " + config.getPath());
            processDirectory(config.getPath(), config.getOutputPath(), config.getTimeoutSeconds());
        }
    }

    /**
     * Analizza e valida gli argomenti della linea di comando.
     *
     * @param args array di argomenti da analizzare
     * @return configurazione validata o null se si verificano errori
     */
    private static CommandLineResult parseCommandLineArguments(String[] args) {
        CommandLineParser parser = new CommandLineParser();

        try {
            return parser.parse(args);
        } catch (IllegalArgumentException e) {
            LOGGER.warning("Errore nei parametri: " + e.getMessage());
            System.out.println("Errore: " + e.getMessage());
            return null;
        }
    }


    /**
     * Elabora tutti i file .txt in una directory specificata.
     *
     * Scansiona la directory, identifica tutti i file con estensione .txt e li elabora
     * sequenzialmente. Fornisce un riepilogo completo delle operazioni eseguite.
     *
     * @param dirPath percorso della directory da elaborare
     * @param outputPath percorso della directory di output (opzionale)
     * @param timeoutSeconds timeout in secondi per ogni formula
     */
    private static void processDirectory(String dirPath, String outputPath, int timeoutSeconds) {
        LOGGER.info("Inizio elaborazione directory: " + dirPath);

        // Validazione directory
        DirectoryValidator validator = new DirectoryValidator();
        if (!validator.validateInputDirectory(dirPath)) {
            return;
        }

        try {
            // Raccolta file da elaborare
            List<File> txtFiles = collectTxtFiles(dirPath);
            if (txtFiles.isEmpty()) {
                System.out.println("Nessun file .txt trovato nella directory specificata.");
                return;
            }

            // Elaborazione batch
            BatchProcessor processor = new BatchProcessor(outputPath, timeoutSeconds);
            BatchResult batchResult = processor.processBatch(txtFiles);

            // Riepilogo risultati
            displayBatchSummary(batchResult);

        } catch (IOException e) {
            LOGGER.log(Level.SEVERE, "Errore nell'accesso alla directory", e);
            System.out.println("Errore durante l'accesso alla directory: " + e.getMessage());
        }
    }

    /**
     * Raccoglie tutti i file .txt dalla directory specificata.
     *
     * @param dirPath percorso della directory
     * @return lista dei file .txt trovati
     * @throws IOException se si verificano errori di I/O
     */
    private static List<File> collectTxtFiles(String dirPath) throws IOException {
        List<File> txtFiles = new ArrayList<>();

        System.out.println("Ricerca dei file .txt nella directory...");

        try (Stream<Path> pathStream = Files.list(Paths.get(dirPath))) {
            txtFiles = pathStream
                    .filter(path -> path.toString().toLowerCase().endsWith(".txt"))
                    .map(Path::toFile)
                    .sorted(Comparator.comparing(File::getName)) // Ordinamento alfabetico
                    .collect(ArrayList::new, ArrayList::add, ArrayList::addAll);
        }

        System.out.println("Trovati " + txtFiles.size() + " file .txt da elaborare.");
        return txtFiles;
    }

    /**
     * Mostra il riepilogo dell'elaborazione batch.
     *
     * @param result risultati dell'elaborazione batch
     */
    private static void displayBatchSummary(BatchResult result) {
        System.out.println("\n=== RIEPILOGO ELABORAZIONE DIRECTORY ===");
        System.out.println("File .txt trovati: " + result.getTotalFiles());
        System.out.println("File elaborati con successo: " + result.getSuccessCount());
        System.out.println("File con timeout: " + result.getTimeoutCount());
        System.out.println("File con errori: " + result.getErrorCount());

        // Calcolo percentuali
        if (result.getTotalFiles() > 0) {
            double successRate = (double) result.getSuccessCount() / result.getTotalFiles() * 100;
            System.out.printf("Tasso di successo: %.1f%%\n", successRate);
        }

        System.out.println("=========================================\n");
    }


    /**
     * Elabora un singolo file TXT contenente una formula logica.
     *   - Lettura e parsing della formula logica
     *   - Conversione in forma normale congiuntiva (CNF)
     *   - Risoluzione SAT con algoritmo CDCL
     *   - Salvataggio dei risultati e statistiche
     *
     * @param filePath percorso del file da elaborare
     * @param outputPath percorso della directory di output (opzionale)
     * @param timeoutSeconds timeout in secondi per la risoluzione
     * @return risultato dell'elaborazione
     */
    private static ProcessResult processFile(String filePath, String outputPath, int timeoutSeconds) {
        LOGGER.info("Inizio elaborazione file: " + filePath);

        try {
            // Pipeline di elaborazione del file
            FileProcessor processor = new FileProcessor(filePath, outputPath, timeoutSeconds);
            return processor.execute();

        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Errore durante l'elaborazione del file: " + filePath, e);
            System.out.println("Errore durante l'elaborazione: " + e.getMessage());
            return ProcessResult.error();
        }
    }

    /**
     * Visualizza le informazioni di aiuto sull'utilizzo del programma.
     */
    private static void printHelp() {
        System.out.println("\n=== SOLUTORE SAT CDCL v1.4.0 ===");
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
        System.out.println("  -h              Mostra questa guida\n");

        System.out.println("ESEMPI:");
        System.out.println("  java -jar solutore_SAT.jar -f formula.txt");
        System.out.println("  java -jar solutore_SAT.jar -d ./formule/ -o ./risultati/ -t 30\n");

        System.out.println("NOTE:");
        System.out.println("  • Le opzioni -f e -d sono mutuamente esclusive");
        System.out.println("  • L'opzione -o è opzionale per entrambe le modalità");
        System.out.println("  • Se -o non è specificata, i risultati saranno salvati");
        System.out.println("    nella stessa directory dell'input");
        System.out.println("  • Il solver supporta formule in logica proposizionale");
        System.out.println("    con operatori: AND, OR, NOT, ->, <->");
        System.out.println("\n=====================================\n");
    }


    /**
     * Parser per gli argomenti della linea di comando.
     * Incapsula la logica di parsing e validazione dei parametri.
     */
    private static class CommandLineParser {

        /**
         * Analizza gli argomenti della linea di comando.
         *
         * @param args array di argomenti
         * @return configurazione validata
         * @throws IllegalArgumentException se gli argomenti non sono validi
         */
        public CommandLineResult parse(String[] args) {
            String path = null;
            String outputPath = null;
            boolean isFileMode = false;
            boolean isDirectoryMode = false;
            int timeoutSeconds = DEFAULT_TIMEOUT_SECONDS;

            for (int i = 0; i < args.length; i++) {
                switch (args[i]) {
                    case HELP_PARAM:
                        printHelp();
                        return null;

                    case FILE_PARAM:
                        validateMutualExclusion(isDirectoryMode, "Impossibile specificare sia -f che -d");
                        path = parseNextArgument(args, i++, "file");
                        validateFile(path);
                        isFileMode = true;
                        break;

                    case DIR_PARAM:
                        validateMutualExclusion(isFileMode, "Impossibile specificare sia -f che -d");
                        path = parseNextArgument(args, i++, "directory");
                        validateDirectory(path);
                        isDirectoryMode = true;
                        break;

                    case OUTPUT_PARAM:
                        outputPath = parseNextArgument(args, i++, "directory di output");
                        validateOutputDirectory(outputPath);
                        break;

                    case TIMEOUT_PARAM:
                        timeoutSeconds = parseTimeout(args, i++);
                        break;

                    default:
                        throw new IllegalArgumentException("Parametro sconosciuto: " + args[i] +
                                ". Usa -h per l'aiuto");
                }
            }

            return validateAndCreateResult(path, outputPath, isFileMode, isDirectoryMode, timeoutSeconds);
        }


        /**
         * Garantisce che l'utente specifichi solo una modalità operativa alla volta.
         *
         * @param conflictingFlag true se l'opzione conflittuale è già stata specificata
         * @param message messaggio base di errore da personalizzare
         * @throws IllegalArgumentException se viene rilevato un conflitto
         */
        private void validateMutualExclusion(boolean conflictingFlag, String message) {
            // Verifica se l'utente ha già specificato un'opzione incompatibile
            if (conflictingFlag) {
                throw new IllegalArgumentException(message + ". Usa solo una delle due opzioni.");
            }
        }

        /**
         * Estrae il prossimo argomento dalla linea di comando con validazione.
         *
         * @param args array completo degli argomenti della linea di comando
         * @param currentIndex indice del flag corrente (es. posizione di "-f")
         * @param argumentType descrizione del tipo di argomento per messaggio errore
         * @return valore dell'argomento successivo al flag
         * @throws IllegalArgumentException se l'argomento successivo non esiste
         */
        private String parseNextArgument(String[] args, int currentIndex, String argumentType) {
            // Verifica che esista un elemento successivo nell'array
            if (currentIndex + 1 >= args.length) {
                throw new IllegalArgumentException("Parametro " + args[currentIndex] +
                        " fornito senza specificare " + argumentType);
            }

            // Restituisce l'argomento nella posizione successiva al flag
            return args[currentIndex + 1];
        }

        /**
         * Validazione e conversione del parametro timeout.
         *
         * @param args array degli argomenti della linea di comando
         * @param currentIndex indice del flag -t
         * @return valore di timeout validato e convertito
         * @throws IllegalArgumentException se il valore è assente, non numerico o fuori range
         */
        private int parseTimeout(String[] args, int currentIndex) {
            // Utilizza il parser generico per ottenere il valore dopo -t
            // Se manca, parseNextArgument lancerà l'eccezione appropriata
            String timeoutStr = parseNextArgument(args, currentIndex, "numero di secondi");

            try {
                // Tenta di convertire la stringa in intero
                int timeout = Integer.parseInt(timeoutStr);

                // Verifica che il timeout sia almeno il minimo configurato
                if (timeout < MIN_TIMEOUT_SECONDS) {
                    throw new IllegalArgumentException("Il timeout deve essere almeno " +
                            MIN_TIMEOUT_SECONDS + " secondi");
                }

                return timeout;

            } catch (NumberFormatException e) {
                throw new IllegalArgumentException("Valore timeout non valido: " + timeoutStr);
            }
        }

        /**
         * Controllo coerenza globale e creazione risultato.
         *
         * @param path percorso del file o directory da elaborare
         * @param outputPath directory di output (può essere null)
         * @param isFileMode true se modalità file singolo attiva
         * @param isDirectoryMode true se modalità directory attiva
         * @param timeoutSeconds timeout validato in secondi
         * @return oggetto CommandLineResult con tutti i parametri validati
         * @throws IllegalArgumentException se mancano parametri essenziali
         */
        private CommandLineResult validateAndCreateResult(String path, String outputPath,
                                                          boolean isFileMode, boolean isDirectoryMode,
                                                          int timeoutSeconds) {

            // Verifica che l'utente abbia specificato almeno un file o directory da elaborare
            if (path == null) {
                throw new IllegalArgumentException("Nessun file o directory specificati. Usa -h per l'aiuto");
            }

            return new CommandLineResult(path, outputPath, isFileMode, isDirectoryMode, timeoutSeconds);
        }

        /**
         * Verifica completa di accessibilità e tipo file.
         *
         * @param filePath percorso del file da validare
         * @throws IllegalArgumentException se il file non passa uno dei controlli
         */
        private void validateFile(String filePath) {
            // Crea un oggetto File per accedere alle operazioni del filesystem
            File file = new File(filePath);

            // Verifica che il percorso corrisponda a un elemento esistente
            if (!file.exists()) {
                throw new IllegalArgumentException("Il file specificato non esiste: " + filePath);
            }

            // Verifica che l'elemento sia effettivamente un file (non directory)
            if (!file.isFile()) {
                throw new IllegalArgumentException("Il percorso specificato non è un file: " + filePath);
            }

            // Verifica i permessi di lettura per il processo corrente
            if (!file.canRead()) {
                throw new IllegalArgumentException("Il file specificato non è leggibile: " + filePath);
            }
        }

        /**
         * Verifica completa di accessibilità directory di input.
         *
         * @param dirPath percorso della directory da validare
         * @throws IllegalArgumentException se la directory non passa i controlli
         */
        private void validateDirectory(String dirPath) {
            // Crea un oggetto File per accedere alla directory
            File dir = new File(dirPath);

            // Verifica che il percorso esista nel filesystem
            if (!dir.exists()) {
                throw new IllegalArgumentException("La directory specificata non esiste: " + dirPath);
            }

            // Verifica che l'elemento sia una directory (non file)
            if (!dir.isDirectory()) {
                throw new IllegalArgumentException("Il percorso specificato non è una directory: " + dirPath);
            }

            // Verifica permessi di lettura (necessari per listing contenuto)
            if (!dir.canRead()) {
                throw new IllegalArgumentException("La directory specificata non è leggibile: " + dirPath);
            }
        }

        /**
         * Gestione intelligente della directory di output.
         *
         * @param dirPath percorso della directory di output
         * @throws IllegalArgumentException se la creazione/validazione fallisce
         */
        private void validateOutputDirectory(String dirPath) {
            // Crea un oggetto File per accedere alla directory
            File dir = new File(dirPath);

            if (!dir.exists()) {
                LOGGER.info("Creazione directory di output: " + dirPath);
                System.out.println("Creazione directory di output: " + dirPath);

                // Crea l'intera gerarchia di directory se necessario
                if (!dir.mkdirs()) {
                    throw new IllegalArgumentException("Impossibile creare la directory di output: " + dirPath);
                }

                System.out.println("Directory di output creata con successo.");

            } else if (!dir.isDirectory()) {
                // Il percorso esiste già ma è un file, non una directory
                throw new IllegalArgumentException("Il percorso di output non è una directory: " + dirPath);
            }

            // Verifica che la directory (esistente o appena creata) sia scrivibile
            if (!dir.canWrite()) {
                throw new IllegalArgumentException("La directory di output non è scrivibile: " + dirPath);
            }
        }
    }

    /**
     * Validatore per directory.
     */
    private static class DirectoryValidator {

        /**
         * Valida una directory di input.
         *
         * @param dirPath percorso da validare
         * @return true se valida, false altrimenti
         */
        public boolean validateInputDirectory(String dirPath) {
            File dir = new File(dirPath);

            // Verifica se il percorso esiste ed è una directory
            if (!dir.exists() || !dir.isDirectory()) {
                LOGGER.warning("Directory non valida: " + dirPath);
                System.out.println("Errore: la directory specificata non esiste o non è una directory: " + dirPath);
                return false;
            }

            // Verifica se la directory può essere letta
            if (!dir.canRead()) {
                LOGGER.warning("Directory non leggibile: " + dirPath);
                System.out.println("Errore: la directory specificata non è leggibile: " + dirPath);
                return false;
            }

            return true;
        }
    }

    /**
     * Processore per elaborazione batch di file.
     */
    private static class BatchProcessor {
        private final String outputPath;
        private final int timeoutSeconds;

        public BatchProcessor(String outputPath, int timeoutSeconds) {
            this.outputPath = outputPath;
            this.timeoutSeconds = timeoutSeconds;
        }

        /**
         * Elabora un batch di file.
         *
         * @param files lista di file .txt da elaborare sequenzialmente
         * @return BatchResult con statistiche aggregate dell'elaborazione
         */
        public BatchResult processBatch(List<File> files) {
            // Crea l'oggetto risultato con il conteggio totale di file da elaborare
            BatchResult result = new BatchResult(files.size());

            System.out.println("Timeout per file: " + timeoutSeconds + " secondi\n");

            // Processa ogni file sequenzialmente mantenendo isolamento degli errori
            for (File file : files) {
                try {
                    System.out.println("Elaborazione del file: " + file.getName());

                    ProcessResult fileResult = processFile(file.getAbsolutePath(), outputPath, timeoutSeconds);

                    if (fileResult.isSuccess()) {
                        // File elaborato correttamente (formula SAT o UNSAT determinata)
                        result.incrementSuccess();

                    } else if (fileResult.isTimeout()) {
                        // File non completato entro il limite temporale
                        result.incrementTimeout();

                    } else {
                        // Altri tipi di fallimento (parsing, I/O, errori interni)
                        result.incrementError();
                    }

                } catch (Exception e) {
                    LOGGER.log(Level.WARNING, "Errore durante elaborazione file: " + file.getName(), e);

                    System.out.println("Errore durante l'elaborazione del file " + file.getName() +
                            ": " + e.getMessage());

                    // Conta questo file come errore nelle statistiche finali
                    result.incrementError();
                }

                System.out.println();
            }

            // Ritorna tutte le statistiche accumulate durante il batch:
            // totale, successi, timeout, errori per analisi finale
            return result;
        }
    }

    /**
     * Processore per singoli file.
     */
    private static class FileProcessor {
        private final String filePath;
        private final String outputPath;
        private final int timeoutSeconds;
        private SATStatistics lastKnownStatistics = null;

        public FileProcessor(String filePath, String outputPath, int timeoutSeconds) {
            this.filePath = filePath;
            this.outputPath = outputPath;
            this.timeoutSeconds = timeoutSeconds;
        }

        /**
         * Esegue l'elaborazione completa del file.
         *
         * @return risultato dell'elaborazione
         * @throws Exception se si verificano errori
         */
        public ProcessResult execute() throws Exception {
            System.out.println("\n=== ELABORAZIONE FILE ===");
            System.out.println("File: " + Paths.get(filePath).getFileName());
            System.out.println("========================\n");

            // Step 1: Lettura formula
            String formulaText = readLogicFormula();

            // Step 2: Conversione CNF
            CNFConversionResult cnfResult = convertToCNF(formulaText);

            // Step 3: Salvataggio CNF
            saveCNFFormula(cnfResult.getCnfString());

            // Step 4: Risoluzione SAT
            SATResult satResult = solveSATWithTimeout(cnfResult.getCnfFormula());

            if (satResult == null) {
                return handleTimeout();
            }

            // Step 5: Salvataggio risultati
            saveResults(satResult, cnfResult.getCnfFormula());

            // Step 6: Display statistiche
            displayStatistics(satResult, cnfResult.getCnfFormula());

            return ProcessResult.success();
        }


        /**
         * Lettura e caricamento della formula logica dal file di input.
         *
         * @return contenuto della formula come stringa normalizzata
         * @throws IOException se il file non è accessibile o leggibile
         */
        private String readLogicFormula() throws IOException {
            System.out.println("1. Lettura della formula logica...");

            String content = Files.readString(Path.of(filePath)).trim();        // Sono rimossi gli spazi bianchi iniziali e finali per normalizzazione

            LOGGER.info("Formula letta: " + content);

            // Restituisce il contenuto normalizzato pronto per il parsing
            return content;
        }

        /**
         * Conversione della formula da notazione infix a forma normale congiuntiva (CNF).
         *
         * @param formulaText formula in notazione infix da convertire
         * @return oggetto contenente sia la rappresentazione CNF che la stringa formattata
         * @throws Exception se il parsing fallisce o la formula è malformata
         */
        private CNFConversionResult convertToCNF(String formulaText) throws Exception {
            System.out.println("2. Conversione in CNF...");

            // Crea uno stream di caratteri dalla stringa di input
            CharStream input = CharStreams.fromString(formulaText);

            // Con il lexer vengono riconosciuti gli operatori logici, variabili, parentesi, ecc.
            LogicFormulaLexer lexer = new LogicFormulaLexer(input);

            // Converte i caratteri in una sequenza di token strutturati
            CommonTokenStream tokens = new CommonTokenStream(lexer);

            // Inizializza il parser ANTLR con la grammatica della logica proposizionale
            org.sat.antlr.org.sat.parser.LogicFormulaParser parser =
                    new org.sat.antlr.org.sat.parser.LogicFormulaParser(tokens);

            // Genera l'albero di sintassi astratta per la formula
            ParseTree tree = parser.formula();

            // Crea il convertitore che implementa il Visitor Pattern
            LogicFormulaParser converter = new LogicFormulaParser();

            // Attraversa l'albero di sintassi astratta e costruisce la rappresentazione interna
            CNFConverter formula = converter.visit(tree);

            // Applica gli algoritmi di conversione in forma normale congiuntiva
            CNFConverter cnfFormula = formula.toCNF();

            // Genera la rappresentazione testuale della formula CNF
            String cnfString = cnfFormula.toString();

            LOGGER.info("Formula CNF generata: " + cnfString);

            // Incapsula entrambe le rappresentazioni per uso downstream
            return new CNFConversionResult(cnfFormula, cnfString);
        }

        /**
         * Persistenza della formula CNF su file system.
         *
         * @param cnfString rappresentazione testuale della formula CNF
         * @throws IOException se si verificano errori di I/O durante la scrittura
         */
        private void saveCNFFormula(String cnfString) throws IOException {
            System.out.println("3. Salvataggio formula CNF...");

            // Ottiene il percorso della directory CNF
            Path cnfDir = getCNFDirectory();

            // Crea la struttura di directory se non esiste
            Files.createDirectories(cnfDir);

            // Estrae il nome base del file originale (senza estensione)
            String baseFileName = getBaseFileName();

            // Costruisce il percorso completo del file CNF con estensione .cnf
            Path cnfFilePath = cnfDir.resolve(baseFileName + ".cnf");

            try (FileWriter writer = new FileWriter(cnfFilePath.toFile())) {
                // Scrittura diretta della stringa CNF nel file
                writer.write(cnfString);
            }

            LOGGER.info("Formula CNF salvata in: " + cnfFilePath);
        }

        /**
         * Risoluzione SAT con algoritmo CDCL e gestione timeout.
         *
         * @param cnfFormula rappresentazione CNF della formula da risolvere
         * @return risultato SAT (SAT/UNSAT con modello/prova) o null se timeout
         */
        private SATResult solveSATWithTimeout(CNFConverter cnfFormula) {
            System.out.println("4. Risoluzione SAT con CDCL (timeout: " + timeoutSeconds + "s)...");

            // Crea un ExecutorService con singolo thread per isolamento
            ExecutorService executor = Executors.newSingleThreadExecutor();

            // Inizializza il solver CDCL con la formula CNF
            CDCLSolver solver = new CDCLSolver(cnfFormula);

            try {
                // Incapsula la chiamata al solver in un Callable per esecuzione asincrona
                Callable<SATResult> solverTask = () -> {
                    // Qui avviene la risoluzione SAT
                    return solver.solve();
                };

                // Sottomette il task all'executor e ottiene un Future per controllo
                Future<SATResult> future = executor.submit(solverTask);

                // Attende il risultato per il tempo specificato dal timeout
                // Se il timeout scade, viene lanciata TimeoutException
                return future.get(timeoutSeconds, TimeUnit.SECONDS);

            } catch (TimeoutException e) {
                LOGGER.warning("Timeout raggiunto dopo " + timeoutSeconds + " secondi");

                // Tenta di recuperare statistiche parziali per analisi
                try {
                    // Si richiama un metodo specializzato per stato intermedio
                    lastKnownStatistics = solver.getPartialStatistics();
                } catch (Exception statEx) {
                    // Crea statistiche vuote se il recupero fallisce
                    LOGGER.warning("Impossibile ottenere statistiche parziali: " + statEx.getMessage());
                    lastKnownStatistics = new SATStatistics();
                }

                // Ritorna null per indicare timeout al chiamante
                return null;

            } catch (Exception e) {
                LOGGER.log(Level.SEVERE, "Errore durante risoluzione SAT", e);
                throw new RuntimeException("Errore durante la risoluzione SAT", e);

            } finally {
                // Termina immediatamente tutti i task in esecuzione
                executor.shutdownNow();
            }
        }

        /**
         * Elaborazione del caso di superamento limite temporale.
         *
         * @return ProcessResult che indica timeout per il controllo del flusso
         * @throws IOException se si verificano errori durante il salvataggio
         */
        private ProcessResult handleTimeout() throws IOException {
            System.out.println("TIMEOUT: Superato il limite di " + timeoutSeconds + " secondi");

            // Crea un file di risultato specifico per il caso di timeout
            saveTimeoutResult();

            // Ritorna un ProcessResult che indica timeout per il controllo del flusso
            return ProcessResult.timeout();
        }

        /**
         * Salvataggio completo dei risultati della risoluzione SAT.
         *
         * @param result risultato della risoluzione SAT
         * @param cnfFormula formula CNF risolta (per statistiche)
         * @throws IOException se si verificano errori di I/O durante la scrittura
         */
        private void saveResults(SATResult result, CNFConverter cnfFormula) throws IOException {
            System.out.println("5. Salvataggio dei risultati...");

            // Ottiene/crea la directory per i risultati
            Path resultDir = getResultDirectory();
            Files.createDirectories(resultDir);

            // Genera il nome del file di risultato basato sull'input
            String baseFileName = getBaseFileName();
            Path resultFilePath = resultDir.resolve(baseFileName + ".result");

            try (FileWriter writer = new FileWriter(resultFilePath.toFile())) {
                // Scrittura a sezioni del report finale
                writeResultHeader(writer);              // Metadati e informazioni file
                writeResultContent(writer, result);     // Risultato SAT/UNSAT principale
                writeResultFooter(writer, result);      // Statistiche e prestazioni
            }

            LOGGER.info("Risultati salvati in: " + resultFilePath);
        }

        /**
         * Visualizzazione finale delle statistiche di elaborazione.
         *
         * @param result risultato della risoluzione SAT
         * @param cnfFormula formula CNF per estrazione metadati
         */
        private void displayStatistics(SATResult result, CNFConverter cnfFormula) {
            System.out.println("6. Elaborazione completata!\n");

            // Converte il risultato booleano in stringa leggibile
            String resultStr = result.isSatisfiable() ? "SAT" : "UNSAT";

            // Chiama il metodo di stampa delle statistiche
            result.getStatistics().printDetailedStats(
                    extractVariableCount(cnfFormula),   // Numero variabili uniche
                    extractClauseCount(cnfFormula),     // Numero clausole totali
                    resultStr                           // "SAT" o "UNSAT"
            );
        }

        /**
         * Creazione report specifico per casi di timeout.
         *
         * @throws IOException se si verificano errori durante il salvataggio
         */
        private void saveTimeoutResult() throws IOException {
            Path resultDir = getResultDirectory();
            Files.createDirectories(resultDir);

            String baseFileName = getBaseFileName();
            Path resultFilePath = resultDir.resolve(baseFileName + ".result");

            try (FileWriter writer = new FileWriter(resultFilePath.toFile())) {
                // Utilizza un metodo specializzato per il formato timeout
                writeTimeoutResult(writer);
            }
        }

        /**
         * Scrittura dell'intestazione standardizzata del report.
         *
         * @param writer FileWriter per scrittura del contenuto
         * @throws IOException se si verificano errori di I/O
         */
        private void writeResultHeader(FileWriter writer) throws IOException {
            writer.write("----------------------\n");
            writer.write("| RISOLUZIONE SAT |\n");
            writer.write("----------------------\n");

            // Estrae solo il nome del file originale dal percorso completo
            String originalFileName = Paths.get(filePath).getFileName().toString();
            String cnfFileName = getBaseFileName() + ".cnf";

            // Scrive i riferimenti ai file per tracciabilità
            writer.write("-> File originale: " + originalFileName + "\n");
            writer.write("-> File cnf: " + cnfFileName + "\n");

            writer.write("\n~~~~~~~~~~~~~~~\n\n");
        }

        /**
         * Scrittura del contenuto principale del risultato.
         *
         * @param writer FileWriter per scrittura del contenuto
         * @param result risultato SAT da formattare
         * @throws IOException se si verificano errori di I/O
         */
        private void writeResultContent(FileWriter writer, SATResult result) throws IOException {
            if (result.isSatisfiable()) {
                // CASO SAT
                writer.write("La formula CNF è SAT.\n");
                writer.write("Modello = {");

                // Verifica disponibilità del modello
                if (result.getAssignment() != null && !result.getAssignment().isEmpty()) {
                    // Ordina le variabili alfabeticamente per output consistente
                    // Converte ogni assegnamento in formato "variabile = valore"
                    String modelString = result.getAssignment().entrySet().stream()
                            .sorted(Map.Entry.comparingByKey())  // Ordinamento alfabetico
                            .map(entry -> entry.getKey() + " = " + (entry.getValue() ? "true" : "false"))
                            .collect(java.util.stream.Collectors.joining(", "));
                    writer.write(modelString);
                } else {
                    writer.write("nessun modello disponibile");
                }

                writer.write("}\n");

            } else {
                // CASO UNSAT
                writer.write("La formula CNF è UNSAT.\n");
                writer.write("Prova generata:\n");

                // Verifica disponibilità della prova
                if (result.getProof() != null && !result.getProof().trim().isEmpty()) {
                    // Scrive la prova completa di insoddisfacibilità
                    writer.write(result.getProof());
                } else {
                    writer.write("Nessuna prova dettagliata disponibile.\n");
                }
            }
        }

        /**
         * Scrittura delle statistiche di esecuzione.
         *
         * Aggiunge le metriche di performance e le statistiche di esecuzione
         * per analisi delle prestazioni e debugging.
         *
         * @param writer FileWriter per scrittura del contenuto
         * @param result risultato SAT per estrazione statistiche
         * @throws IOException se si verificano errori di I/O
         */
        private void writeResultFooter(FileWriter writer, SATResult result) throws IOException {
            writer.write("\n~~~~~~~~~~~~~~~\n\n");

            // Estraggo le statistiche
            SATStatistics stats = result.getStatistics();

            writer.write("Decisioni effettuate: " + stats.getDecisions() + "\n");
            writer.write("Conflitti: " + stats.getConflicts() + "\n");
            writer.write("Tempo di risoluzione della formula CNF: " + stats.getExecutionTimeMs() + " millisecondi\n");
        }

        /**
         * Scrittura report specializzato per timeout.
         *
         * @param writer FileWriter per scrittura del contenuto
         * @throws IOException se si verificano errori di I/O
         */
        private void writeTimeoutResult(FileWriter writer) throws IOException {
            writer.write("----------------------\n");
            writer.write("| RISOLUZIONE SAT |\n");
            writer.write("----------------------\n");

            String originalFileName = Paths.get(filePath).getFileName().toString();
            String cnfFileName = getBaseFileName() + ".cnf";

            writer.write("-> File originale: " + originalFileName + "\n");
            writer.write("-> File cnf: " + cnfFileName + "\n");
            writer.write("\n~~~~~~~~~~~~~~~\n\n");

            writer.write("La risoluzione della formula CNF ha superato il tempo limite di " +
                    timeoutSeconds + " secondi.\n");

            writer.write("\n~~~~~~~~~~~~~~~\n\n");

            // Utilizza le statistiche parziali se sono state recuperate con successo
            if (lastKnownStatistics != null) {
                writer.write("Decisioni effettuate: " + lastKnownStatistics.getDecisions() + "\n");
                writer.write("Conflitti: " + lastKnownStatistics.getConflicts() + "\n");
            } else {
                // Quando le statistiche non sono disponibili
                writer.write("Decisioni effettuate: N/A\n");
                writer.write("Conflitti: N/A\n");
            }
        }

        /**
         * Ottiene la directory per file CNF.
         *
         * @return Path della directory CNF
         */
        private Path getCNFDirectory() {
            if (outputPath != null) {
                // Utilizza la directory di output specificata dall'utente
                return Paths.get(outputPath).resolve("CNF");
            } else {
                // Utilizza la directory del file di input
                Path parentDir = Paths.get(filePath).getParent();
                return parentDir != null ? parentDir.resolve("CNF") : Paths.get("CNF");
            }
        }

        /**
         * Ottiene la directory per file di risultato.
         *
         * @return Path della directory RESULT
         */
        private Path getResultDirectory() {
            if (outputPath != null) {
                return Paths.get(outputPath).resolve("RESULT");
            } else {
                Path parentDir = Paths.get(filePath).getParent();
                return parentDir != null ? parentDir.resolve("RESULT") : Paths.get("RESULT");
            }
        }

        /**
         * Estrae il nome base del file senza estensione.
         *
         * @return nome base del file senza estensione
         */
        private String getBaseFileName() {
            // Ottiene il Path del file originale
            Path originalPath = Paths.get(filePath);

            // Estrae solo il nome del file (senza directory)
            String originalFileName = originalPath.getFileName().toString();

            // Rimuove l'estensione trovando l'ultimo punto
            return originalFileName.substring(0, originalFileName.lastIndexOf('.'));
        }
    }

    /**
     * Estrae il numero di variabili uniche dalla formula CNF.
     *
     * @param cnfFormula formula CNF da analizzare
     * @return numero di variabili distinte
     */
    private static int extractVariableCount(CNFConverter cnfFormula) {
        Set<String> variables = new HashSet<>();
        collectVariablesRecursively(cnfFormula, variables);
        return variables.size();
    }

    /**
     * Raccoglie ricorsivamente tutte le variabili dalla formula CNF.
     *
     * @param formula nodo della formula da analizzare
     * @param variables set che accumula le variabili trovate
     */
    private static void collectVariablesRecursively(CNFConverter formula, Set<String> variables) {
        if (formula == null) return;

        switch (formula.type) {
            case ATOM:
                variables.add(formula.atom);
                break;

            case NOT:
                if (formula.operand != null && formula.operand.type == CNFConverter.Type.ATOM) {
                    variables.add(formula.operand.atom);
                } else if (formula.operand != null) {
                    collectVariablesRecursively(formula.operand, variables);
                }
                break;

            case AND:
            case OR:
                if (formula.operands != null) {
                    for (CNFConverter operand : formula.operands) {
                        collectVariablesRecursively(operand, variables);
                    }
                }
                break;

            default:
                // Per altri tipi, esplora operando singolo se presente
                if (formula.operand != null) {
                    collectVariablesRecursively(formula.operand, variables);
                }
                break;
        }
    }

    /**
     * Estrae il numero di clausole dalla formula CNF.
     *
     * @param cnfFormula formula CNF da analizzare
     * @return numero di clausole nella formula
     */
    private static int extractClauseCount(CNFConverter cnfFormula) {
        return countClausesRecursively(cnfFormula);
    }

    /**
     * Conta ricorsivamente il numero di clausole nella formula CNF.
     *
     * @param formula nodo della formula da analizzare
     * @return numero di clausole
     */
    private static int countClausesRecursively(CNFConverter formula) {
        if (formula == null) return 0;

        switch (formula.type) {
            case AND:
                // In una congiunzione, ogni operando è una clausola
                return formula.operands != null ? formula.operands.size() : 0;

            case OR:
            case ATOM:
                // Una singola clausola
                return 1;

            case NOT:
                // NOT atomico conta come una clausola
                if (formula.operand != null && formula.operand.type == CNFConverter.Type.ATOM) {
                    return 1;
                }
                return countClausesRecursively(formula.operand);

            default:
                return 1;
        }
    }

    /**
     * Risultato dell'analisi della linea di comando.
     * Incapsula tutte le informazioni di configurazione estratte dai parametri.
     */
    private static class CommandLineResult {
        private final String path;
        private final String outputPath;
        private final boolean isFileMode;
        private final boolean isDirectoryMode;
        private final int timeoutSeconds;

        /**
         * Costruisce un nuovo risultato di configurazione.
         *
         * @param path percorso del file o directory di input
         * @param outputPath percorso della directory di output (può essere null)
         * @param isFileMode true se modalità file singolo
         * @param isDirectoryMode true se modalità directory
         * @param timeoutSeconds timeout in secondi per ogni elaborazione
         */
        public CommandLineResult(String path, String outputPath, boolean isFileMode,
                                 boolean isDirectoryMode, int timeoutSeconds) {
            this.path = path;
            this.outputPath = outputPath;
            this.isFileMode = isFileMode;
            this.isDirectoryMode = isDirectoryMode;
            this.timeoutSeconds = timeoutSeconds;
        }

        public String getPath() { return path; }
        public String getOutputPath() { return outputPath; }
        public boolean isFileMode() { return isFileMode; }
        public boolean isDirectoryMode() { return isDirectoryMode; }
        public int getTimeoutSeconds() { return timeoutSeconds; }

        @Override
        public String toString() {
            return String.format("CommandLineResult{path='%s', outputPath='%s', fileMode=%s, dirMode=%s, timeout=%d}",
                    path, outputPath, isFileMode, isDirectoryMode, timeoutSeconds);
        }
    }

    /**
     * Risultato dell'elaborazione di un singolo file.
     * Indica il tipo di esito dell'operazione (successo, timeout, errore).
     */
    private static class ProcessResult {
        private final ResultType type;

        /**
         * Tipi di risultato possibili per l'elaborazione.
         */
        private enum ResultType {
            SUCCESS,    // Elaborazione completata con successo
            TIMEOUT,    // Elaborazione interrotta per timeout
            ERROR       // Elaborazione fallita per errore
        }

        private ProcessResult(ResultType type) {
            this.type = type;
        }

        public boolean isSuccess() { return type == ResultType.SUCCESS; }
        public boolean isTimeout() { return type == ResultType.TIMEOUT; }
        public boolean isError() { return type == ResultType.ERROR; }

        public static ProcessResult success() { return new ProcessResult(ResultType.SUCCESS); }
        public static ProcessResult timeout() { return new ProcessResult(ResultType.TIMEOUT); }
        public static ProcessResult error() { return new ProcessResult(ResultType.ERROR); }

        @Override
        public String toString() {
            return "ProcessResult{type=" + type + "}";
        }
    }

    /**
     * Risultato dell'elaborazione batch di più file.
     * Mantiene contatori per diversi tipi di risultato.
     */
    private static class BatchResult {
        private final int totalFiles;
        private int successCount = 0;
        private int timeoutCount = 0;
        private int errorCount = 0;

        /**
         * Costruisce un nuovo risultato batch.
         *
         * @param totalFiles numero totale di file da elaborare
         */
        public BatchResult(int totalFiles) {
            this.totalFiles = totalFiles;
        }

        public void incrementSuccess() { successCount++; }
        public void incrementTimeout() { timeoutCount++; }
        public void incrementError() { errorCount++; }

        public int getTotalFiles() { return totalFiles; }
        public int getSuccessCount() { return successCount; }
        public int getTimeoutCount() { return timeoutCount; }
        public int getErrorCount() { return errorCount; }

        /**
         * Verifica che i contatori siano consistenti.
         *
         * @return true se i contatori sono validi
         */
        public boolean isConsistent() {
            return (successCount + timeoutCount + errorCount) <= totalFiles;
        }

        @Override
        public String toString() {
            return String.format("BatchResult{total=%d, success=%d, timeout=%d, error=%d}",
                    totalFiles, successCount, timeoutCount, errorCount);
        }
    }

    /**
     * Risultato della conversione in CNF.
     * Incapsula sia la rappresentazione oggetto che la stringa della formula CNF.
     */
    private static class CNFConversionResult {
        private final CNFConverter cnfFormula;
        private final String cnfString;

        /**
         * Costruisce un nuovo risultato di conversione CNF.
         *
         * @param cnfFormula rappresentazione oggetto della formula CNF
         * @param cnfString rappresentazione testuale della formula CNF
         */
        public CNFConversionResult(CNFConverter cnfFormula, String cnfString) {
            this.cnfFormula = cnfFormula;
            this.cnfString = cnfString;
        }

        public CNFConverter getCnfFormula() { return cnfFormula; }
        public String getCnfString() { return cnfString; }

        @Override
        public String toString() {
            return "CNFConversionResult{cnfString='" + cnfString + "'}";
        }
    }
}