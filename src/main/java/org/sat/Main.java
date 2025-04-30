package org.sat;

import java.io.File;
import java.util.logging.Logger;
import java.util.logging.Level;

/**
 * Classe principale per l'avvio del solutore SAT.
 * Gestisce i parametri della linea di comando e inizializza il processo di risoluzione.
 *
 * @author Amos Lo Verde
 * @version 1.0.0
 */
public final class Main {

    /** Logger per la registrazione dei messaggi */
    private static final Logger LOGGER = Logger.getLogger(Main.class.getName());

    /** Costante per il parametro di help */
    private static final String HELP_PARAM = "-h";

    /** Costante per il parametro del file */
    private static final String FILE_PARAM = "-f";

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

        // Percorso del file da elaborare
        String filePath = parseCommandLineArgs(args);

        // Avvio dell'elaborazione se è stato specificato un file valido
        if (filePath != null) {
            LOGGER.info(() -> "File CNF specificato: " + filePath);
            System.out.println("File CNF specificato: " + filePath);
            processFile(filePath);
        }
    }

    /**
     * Analizza gli argomenti della linea di comando.
     *
     * @param args array di argomenti da analizzare
     * @return il percorso del file specifico o null se non valido o non specificato
     */
    private static String parseCommandLineArgs(String[] args) {
        String filePath = null;

        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case HELP_PARAM:
                    printHelp();
                    return null;

                case FILE_PARAM:
                    if (i + 1 < args.length) {
                        filePath = args[++i];
                        if (!validateFile(filePath)) {
                            return null;
                        }
                    } else {
                        LOGGER.warning("Parametro -f fornito senza specificare un file.");
                        System.out.println("Errore: parametro -f fornito senza specificare un file.");
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

        return filePath;
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
     * Visualizza le informazioni di aiuto sul corretto utilizzo del programma.
     */
    private static void printHelp() {
        System.out.println("Utilizzo: java -jar solutore_SAT.jar [opzioni]");
        System.out.println("Opzioni disponibili:");
        System.out.println("  -f <file>      Specifica un file .cnf da risolvere");
        System.out.println("  -h             Mostra questo messaggio di help");
    }

    /**
     * Elabora il file CNF specificato.
     * Questo metodo invoca il parser e trasmette i dati al risolutore.
     *
     * @param filePath percorso del file CNF da elaborare
     */
    private static void processFile(String filePath) {
        try {
            LOGGER.info(() -> "Inizio elaborazione del file: " + filePath);
            System.out.println("Elaborazione del file in corso...");

            // TODO: Implementare la logica di parsing e risoluzione
            // FileParser parser = new FileParser(filePath);
            // SatSolver solver = new SatSolver(parser.parse());
            // Result result = solver.solve();

            LOGGER.info("Elaborazione file completata.");
        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Errore durante l'elaborazione del file", e);
            System.out.println("Si è verificato un errore durante l'elaborazione: " + e.getMessage());
        }
    }
}