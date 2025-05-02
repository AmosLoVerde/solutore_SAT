package org.sat;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.sat.antlr.org.sat.parser.LogicFormulaLexer;
import org.sat.antlr.org.sat.parser.LogicFormulaParser;
import org.sat.cnf.CNFConverter;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.logging.Logger;
import java.util.logging.Level;
import java.util.stream.Stream;

/**
 * Classe principale per l'avvio del solutore SAT.
 * Gestisce i parametri della linea di comando e inizializza il processo di risoluzione.
 *
 * @author Amos Lo Verde
 * @version 1.3.0
 */
public final class Main {

    /** Logger per la registrazione dei messaggi */
    private static final Logger LOGGER = Logger.getLogger(Main.class.getName());

    /** Costante per il parametro di help */
    private static final String HELP_PARAM = "-h";

    /** Costante per il parametro del file */
    private static final String FILE_PARAM = "-f";

    /** Costante per il parametro della directory */
    private static final String DIR_PARAM = "-d";

    /** Costante per il parametro della directory di output */
    private static final String OUTPUT_PARAM = "-o";

    /**
     * Costruttore privato per evitare l'istanziazione di una classe utility.
     */
    private Main() {
        // Utility class, non istanziabile
    }

    /**
     * Punto di ingresso principale del programma.
     * Analizza i parametri della linea di comando e avvia il processo appropriato.
     *
     * @param args argomenti dalla linea di comando
     */
    public static void main(String[] args) {
        // Verifica se sono stati forniti parametri
        if (args.length == 0) {
            LOGGER.info("Nessun parametro fornito. Usa -h per visualizzare l'help.");
            System.out.println("Nessun parametro fornito. Usa -h per visualizzare l'help.");
            return;
        }

        // Analizza gli argomenti dalla linea di comando
        CommandLineResult cmdResult = parseCommandLineArgs(args);

        if (cmdResult != null) {
            if (cmdResult.isFileMode()) {
                // Modalità file singolo
                LOGGER.info(() -> "File TXT specificato: " + cmdResult.getPath());
                System.out.println("File TXT specificato: " + cmdResult.getPath());
                if (cmdResult.getOutputPath() != null) {
                    LOGGER.info(() -> "Directory di output specificata: " + cmdResult.getOutputPath());
                    System.out.println("Directory di output specificata: " + cmdResult.getOutputPath());
                }
                processFile(cmdResult.getPath(), cmdResult.getOutputPath());
            } else if (cmdResult.isDirectoryMode()) {
                // Modalità directory
                LOGGER.info(() -> "Directory specificata: " + cmdResult.getPath());
                System.out.println("Directory specificata: " + cmdResult.getPath());
                if (cmdResult.getOutputPath() != null) {
                    LOGGER.info(() -> "Directory di output specificata: " + cmdResult.getOutputPath());
                    System.out.println("Directory di output specificata: " + cmdResult.getOutputPath());
                }
                processDirectory(cmdResult.getPath(), cmdResult.getOutputPath());
            }
        }
    }

    /**
     * Elabora tutti i file .txt in una directory specificata.
     *
     * @param dirPath percorso della directory da elaborare
     * @param outputPath percorso della directory di output (opzionale)
     */
    private static void processDirectory(String dirPath, String outputPath) {
        File dir = new File(dirPath);

        if (!dir.exists() || !dir.isDirectory()) {
            LOGGER.warning(() -> "La directory specificata non esiste o non è una directory: " + dirPath);
            System.out.println("Errore: la directory specificata non esiste o non è una directory: " + dirPath);
            return;
        }

        if (!dir.canRead()) {
            LOGGER.warning(() -> "La directory specificata non è leggibile: " + dirPath);
            System.out.println("Errore: la directory specificata non è leggibile: " + dirPath);
            return;
        }

        try {
            int fileCount = 0;
            int successCount = 0;

            System.out.println("Ricerca dei file .txt nella directory...");

            // Filtra e processa solo i file .txt nella directory
            try (Stream<Path> pathStream = Files.list(dir.toPath())) {
                File[] txtFiles = pathStream
                        .filter(path -> path.toString().toLowerCase().endsWith(".txt"))
                        .map(Path::toFile)
                        .toArray(File[]::new);

                fileCount = txtFiles.length;

                if (fileCount == 0) {
                    LOGGER.info(() -> "Nessun file .txt trovato nella directory: " + dirPath);
                    System.out.println("Nessun file .txt trovato nella directory specificata.");
                    return;
                }

                System.out.println("Trovati " + fileCount + " file .txt da elaborare.");

                // Elabora ogni file .txt trovato
                for (File file : txtFiles) {
                    try {
                        System.out.println("\nElaborazione del file: " + file.getName());
                        processFile(file.getAbsolutePath(), outputPath);
                        successCount++;
                    } catch (Exception e) {
                        LOGGER.log(Level.WARNING, "Errore durante l'elaborazione del file: " + file.getName(), e);
                        System.out.println("Errore durante l'elaborazione del file " + file.getName() + ": " + e.getMessage());
                    }
                }
            }

            System.out.println("\nRiepilogo elaborazione directory:");
            System.out.println("  File .txt trovati: " + fileCount);
            System.out.println("  File elaborati con successo: " + successCount);
            System.out.println("  File con errori: " + (fileCount - successCount));

        } catch (IOException e) {
            LOGGER.log(Level.SEVERE, "Errore nell'accesso alla directory", e);
            System.out.println("Si è verificato un errore durante l'accesso alla directory: " + e.getMessage());
        }
    }

    /**
     * Analizza gli argomenti della linea di comando.
     *
     * @param args array di argomenti da analizzare
     * @return un oggetto CommandLineResult contenente il percorso e la modalità di elaborazione
     */
    private static CommandLineResult parseCommandLineArgs(String[] args) {
        String path = null;
        String outputPath = null;
        boolean isFileMode = false;
        boolean isDirectoryMode = false;

        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case HELP_PARAM:
                    printHelp();
                    return null;

                case FILE_PARAM:
                    // Controlla se l'opzione -d è già stata specificata
                    if (isDirectoryMode) {
                        LOGGER.warning("Impossibile specificare sia -f che -d. Usa solo una delle due opzioni.");
                        System.out.println("Errore: impossibile specificare sia -f che -d. Usa solo una delle due opzioni.");
                        return null;
                    }

                    if (i + 1 < args.length) {
                        path = args[++i];
                        if (!validateFile(path)) {
                            return null;
                        }
                        isFileMode = true;
                    } else {
                        LOGGER.warning("Parametro -f fornito senza specificare un file.");
                        System.out.println("Errore: parametro -f fornito senza specificare un file.");
                        return null;
                    }
                    break;

                case DIR_PARAM:
                    // Controlla se l'opzione -f è già stata specificata
                    if (isFileMode) {
                        LOGGER.warning("Impossibile specificare sia -f che -d. Usa solo una delle due opzioni.");
                        System.out.println("Errore: impossibile specificare sia -f che -d. Usa solo una delle due opzioni.");
                        return null;
                    }

                    if (i + 1 < args.length) {
                        path = args[++i];
                        if (!validateDirectory(path)) {
                            return null;
                        }
                        isDirectoryMode = true;
                    } else {
                        LOGGER.warning("Parametro -d fornito senza specificare una directory.");
                        System.out.println("Errore: parametro -d fornito senza specificare una directory.");
                        return null;
                    }
                    break;

                case OUTPUT_PARAM:
                    if (i + 1 < args.length) {
                        outputPath = args[++i];
                        if (!validateOutputDirectory(outputPath)) {
                            return null;
                        }
                    } else {
                        LOGGER.warning("Parametro -o fornito senza specificare una directory.");
                        System.out.println("Errore: parametro -o fornito senza specificare una directory.");
                        return null;
                    }
                    break;

                default:
                    int finalI = i;
                    LOGGER.warning(() -> "Parametro sconosciuto: " + args[finalI]);
                    System.out.println("Parametro sconosciuto: " + args[i]);
                    System.out.println("Usa -h per visualizzare la lista dei parametri disponibili.");
                    return null;
            }
        }

        if (path != null) {
            return new CommandLineResult(path, outputPath, isFileMode, isDirectoryMode);
        } else {
            LOGGER.warning("Nessun file o directory specificati.");
            System.out.println("Errore: nessun file o directory specificati.");
            System.out.println("Usa -h per visualizzare la lista dei parametri disponibili.");
            return null;
        }
    }

    /**
     * Valida l'esistenza del file specificato.
     *
     * @param filePath percorso del file da validare
     * @return true se il file esiste, false altrimenti
     */
    private static boolean validateFile(String filePath) {
        File file = new File(filePath);
        if (!file.exists()) {
            LOGGER.warning(() -> "Il file specificato non esiste: " + filePath);
            System.out.println("Errore: il file specificato non esiste: " + filePath);
            return false;
        }
        if (!file.isFile()) {
            LOGGER.warning(() -> "Il percorso specificato non è un file: " + filePath);
            System.out.println("Errore: il percorso specificato non è un file: " + filePath);
            return false;
        }
        if (!file.canRead()) {
            LOGGER.warning(() -> "Il file specificato non è leggibile: " + filePath);
            System.out.println("Errore: il file specificato non è leggibile: " + filePath);
            return false;
        }
        return true;
    }

    /**
     * Valida l'esistenza della directory specificata.
     *
     * @param dirPath percorso della directory da validare
     * @return true se la directory esiste, false altrimenti
     */
    private static boolean validateDirectory(String dirPath) {
        File dir = new File(dirPath);
        if (!dir.exists()) {
            LOGGER.warning(() -> "La directory specificata non esiste: " + dirPath);
            System.out.println("Errore: la directory specificata non esiste: " + dirPath);
            return false;
        }
        if (!dir.isDirectory()) {
            LOGGER.warning(() -> "Il percorso specificato non è una directory: " + dirPath);
            System.out.println("Errore: il percorso specificato non è una directory: " + dirPath);
            return false;
        }
        if (!dir.canRead()) {
            LOGGER.warning(() -> "La directory specificata non è leggibile: " + dirPath);
            System.out.println("Errore: la directory specificata non è leggibile: " + dirPath);
            return false;
        }
        return true;
    }

    /**
     * Valida la directory di output specificata.
     * Se la directory non esiste, tenta di crearla.
     *
     * @param dirPath percorso della directory di output da validare
     * @return true se la directory esiste o è stata creata con successo, false altrimenti
     */
    private static boolean validateOutputDirectory(String dirPath) {
        File dir = new File(dirPath);
        if (!dir.exists()) {
            LOGGER.info(() -> "La directory di output non esiste, tentativo di creazione: " + dirPath);
            System.out.println("La directory di output non esiste, tentativo di creazione: " + dirPath);
            if (!dir.mkdirs()) {
                LOGGER.warning(() -> "Impossibile creare la directory di output: " + dirPath);
                System.out.println("Errore: impossibile creare la directory di output: " + dirPath);
                return false;
            }
            LOGGER.info(() -> "Directory di output creata con successo: " + dirPath);
            System.out.println("Directory di output creata con successo: " + dirPath);
        } else if (!dir.isDirectory()) {
            LOGGER.warning(() -> "Il percorso di output specificato non è una directory: " + dirPath);
            System.out.println("Errore: il percorso di output specificato non è una directory: " + dirPath);
            return false;
        }

        // Verifica i permessi di scrittura
        if (!dir.canWrite()) {
            LOGGER.warning(() -> "La directory di output non è scrivibile: " + dirPath);
            System.out.println("Errore: la directory di output non è scrivibile: " + dirPath);
            return false;
        }
        return true;
    }

    /**
     * Visualizza le informazioni di aiuto sul corretto utilizzo del programma.
     */
    private static void printHelp() {
        System.out.println("Utilizzo: java -jar solutore_SAT.jar [opzioni]");
        System.out.println("Opzioni disponibili:");
        System.out.println("  -f <file>       Specifica un file .txt da risolvere");
        System.out.println("  -d <directory>  Specifica una directory con file .txt da risolvere");
        System.out.println("  -o <directory>  Specifica una directory di output per i file CNF (opzionale)");
        System.out.println("  -h              Mostra questo messaggio di help");
        System.out.println("\nNote:");
        System.out.println("  - Le opzioni -f e -d sono mutuamente esclusive.");
        System.out.println("  - L'opzione -o è opzionale e può essere usata sia con -f che con -d.");
        System.out.println("  - Se -o non è specificata, i file CNF saranno salvati in una cartella CNF");
        System.out.println("    nella stessa directory del file di input o della directory di input.");
    }

    /**
     * Elabora il file TXT specificato.
     * Legge la formula logica, la converte in CNF e salva il risultato.
     *
     * @param filePath percorso del file TXT da elaborare
     * @param outputPath percorso della directory di output (opzionale)
     */
    private static void processFile(String filePath, String outputPath) {
        try {
            LOGGER.info(() -> "Inizio elaborazione del file: " + filePath);
            System.out.println("Elaborazione del file in corso...");

            // Leggi il contenuto del file
            String formulaText = readFileContent(filePath);

            // Crea il parser ANTLR e analizza la formula
            CharStream input = CharStreams.fromString(formulaText);
            LogicFormulaLexer lexer = new LogicFormulaLexer(input);
            CommonTokenStream tokens = new CommonTokenStream(lexer);
            LogicFormulaParser parser = new LogicFormulaParser(tokens);
            ParseTree tree = parser.formula();

            // Converti la formula in CNF
            CNFConverter converter = new CNFConverter();
            Object result = converter.visit(tree);
            String cnfFormula = result.toString();

            LOGGER.info("Input originale: " + input);
            LOGGER.info("Formula CNF: " + cnfFormula);

            // Salva la formula CNF in un nuovo file
            saveCNFFormula(filePath, cnfFormula, outputPath);

            LOGGER.info("Elaborazione file completata.");
            System.out.println("Elaborazione file completata con successo.");
            System.out.println("Formula CNF salvata nella cartella specificata.");
        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Errore durante l'elaborazione del file", e);
            System.out.println("Si è verificato un errore durante l'elaborazione: " + e.getMessage());
            throw new RuntimeException("Errore durante l'elaborazione del file", e);
        }
    }

    /**
     * Legge il contenuto del file di testo.
     *
     * @param filePath percorso del file da leggere
     * @return contenuto del file come stringa
     * @throws IOException se si verifica un errore durante la lettura
     */
    private static String readFileContent(String filePath) throws IOException {
        LOGGER.info(() -> "Lettura del file: " + filePath);
        return Files.readString(Path.of(filePath)).trim();
    }

    /**
     * Salva la formula CNF in un nuovo file.
     *
     * @param originalFilePath percorso del file originale
     * @param cnfFormula formula CNF da salvare
     * @param outputPath percorso della directory di output (opzionale)
     * @throws IOException se si verifica un errore durante la scrittura
     */
    private static void saveCNFFormula(String originalFilePath, String cnfFormula, String outputPath) throws IOException {
        Path cnfDir;

        if (outputPath != null) {
            // Usa la directory di output specificata, e aggiungi sempre la sottodirectory CNF
            cnfDir = Paths.get(outputPath).resolve("CNF");
        } else {
            // Ottieni il percorso della directory del file originale
            Path originalPath = Paths.get(originalFilePath);
            Path parentDir = originalPath.getParent();

            // Crea la directory CNF se non esiste
            cnfDir = parentDir != null ?
                    parentDir.resolve("CNF") :
                    Paths.get("CNF");
        }

        // Assicurati che la directory CNF esista
        Files.createDirectories(cnfDir);

        // Ottieni il nome del file originale senza estensione
        Path originalPath = Paths.get(originalFilePath);
        String originalFileName = originalPath.getFileName().toString();
        String baseFileName = originalFileName.substring(0, originalFileName.lastIndexOf('.'));

        // Crea il nuovo file .cnf
        Path cnfFilePath = cnfDir.resolve(baseFileName + ".cnf");

        LOGGER.info(() -> "Salvataggio della formula CNF nel file: " + cnfFilePath);

        // Scrivi la formula CNF nel nuovo file
        try (FileWriter writer = new FileWriter(cnfFilePath.toFile())) {
            writer.write(cnfFormula);
        }
    }

    /**
     * Classe interna per rappresentare il risultato dell'analisi della linea di comando.
     */
    private static class CommandLineResult {
        private final String path;
        private final String outputPath;
        private final boolean isFileMode;
        private final boolean isDirectoryMode;

        /**
         * Costruttore per CommandLineResult.
         *
         * @param path percorso del file o della directory
         * @param outputPath percorso della directory di output (opzionale)
         * @param isFileMode true se si tratta di un file
         * @param isDirectoryMode true se si tratta di una directory
         */
        public CommandLineResult(String path, String outputPath, boolean isFileMode, boolean isDirectoryMode) {
            this.path = path;
            this.outputPath = outputPath;
            this.isFileMode = isFileMode;
            this.isDirectoryMode = isDirectoryMode;
        }

        /**
         * Restituisce il percorso del file o della directory.
         *
         * @return percorso come stringa
         */
        public String getPath() {
            return path;
        }

        /**
         * Restituisce il percorso della directory di output.
         *
         * @return percorso di output come stringa o null se non specificato
         */
        public String getOutputPath() {
            return outputPath;
        }

        /**
         * Verifica se è attiva la modalità file.
         *
         * @return true se è attiva la modalità file
         */
        public boolean isFileMode() {
            return isFileMode;
        }

        /**
         * Verifica se è attiva la modalità directory.
         *
         * @return true se è attiva la modalità directory
         */
        public boolean isDirectoryMode() {
            return isDirectoryMode;
        }
    }
}