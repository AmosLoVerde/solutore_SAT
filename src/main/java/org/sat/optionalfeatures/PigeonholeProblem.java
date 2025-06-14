package org.sat.optionalfeatures;

import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Logger;
import java.util.logging.Level;

/**
 * GENERATORE PIGEONHOLE PROBLEM - Sistema per generazione automatica istanze
 *
 * Implementa la generazione automatica di istanze del classico "Pigeonhole Problem"
 * per testing e benchmarking di solutori SAT. Il problema codifica la impossibilità
 * matematica di inserire n+1 piccioni in n buche quando ogni buco può contenere
 * al più un piccione.
 *
 * FORMULAZIONE LOGICA:
 * - Variabili: p_ij rappresenta "piccione i è nella buca j"
 * - Vincoli positivi: ogni piccione deve essere in almeno una buca
 * - Vincoli negativi: ogni buca può contenere al più un piccione
 *
 * CARATTERISTICHE GENERATE:
 * - Tutte le istanze sono UNSAT per costruzione matematica
 * - Complessità crescente con n (utile per benchmark performance)
 * - Formato compatibile con parser del solutore SAT
 * - Output organizzato in directory strutturata
 *
 */
public class PigeonholeProblem {

    private static final Logger LOGGER = Logger.getLogger(PigeonholeProblem.class.getName());

    //region CONFIGURAZIONE E COSTANTI

    /** Nome directory contenitore per istanze generate */
    private static final String PIGEONHOLE_DIR = "PIGEONHOLE";

    /** Prefisso nome file per istanze generate */
    private static final String FILE_PREFIX = "pigeonhole_";

    /** Estensione file per istanze generate */
    private static final String FILE_EXTENSION = ".txt";

    //endregion

    //region STATO GENERAZIONE

    /**
     * Directory di output configurata per salvataggio istanze.
     * Null fino a quando non viene configurata tramite setOutputDirectory().
     */
    private String outputDirectory;

    /**
     * Contatore istanze generate con successo durante sessione corrente.
     * Utilizzato per statistiche e validazione completamento.
     */
    private int generatedInstances;

    /**
     * Log dettagliato delle operazioni di generazione per debugging e reporting.
     * Contiene cronologia completa del processo di generazione.
     */
    private StringBuilder generationLog;

    //endregion

    //region INIZIALIZZAZIONE

    /**
     * Inizializza generatore Pigeonhole Problem con stato pulito.
     * Prepara tutte le strutture dati per nuova sessione di generazione.
     */
    public PigeonholeProblem() {
        resetGenerationState();
        LOGGER.fine("PigeonholeProblem inizializzato per generazione istanze");
    }

    /**
     * Reset completo dello stato per riutilizzo del generatore.
     * Pulisce tutti i dati di precedenti generazioni mantenendo configurazione.
     */
    private void resetGenerationState() {
        this.outputDirectory = null;
        this.generatedInstances = 0;
        this.generationLog = new StringBuilder();
    }

    /**
     * Configura directory di output per salvataggio istanze generate.
     *
     * @param outputPath percorso directory base dove creare sottodirectory PIGEONHOLE
     * @throws IllegalArgumentException se outputPath null o non valido
     */
    public void setOutputDirectory(String outputPath) {
        if (outputPath == null || outputPath.trim().isEmpty()) {
            throw new IllegalArgumentException("Directory output non può essere null o vuota");
        }

        this.outputDirectory = outputPath.trim();
        generationLog.append("Directory output configurata: ").append(outputDirectory).append("\n");

        LOGGER.fine("Directory output configurata: " + outputDirectory);
    }

    //endregion

    //region INTERFACCIA PUBBLICA PRINCIPALE

    /**
     * METODO PRINCIPALE - Genera numero specificato di istanze Pigeonhole Problem
     *
     * Crea N istanze del problema con dimensioni crescenti da 1 a N, dove ogni
     * istanza i rappresenta il problema di inserire i+1 piccioni in i buche.
     * Tutte le istanze generate sono UNSAT per il principio matematico del
     * pigeonhole principle.
     *
     * PROCESSO GENERAZIONE:
     * 1. Validazione parametri e configurazione ambiente
     * 2. Creazione directory output strutturata
     * 3. Generazione sequenziale istanze con dimensioni crescenti
     * 4. Salvataggio file formattati per parser solutore
     * 5. Validazione completezza e generazione report finale
     *
     * @param numberOfProblems numero istanze da generare (1 ≤ n ≤ 100)
     * @throws IllegalArgumentException se numberOfProblems non valido
     * @throws IllegalStateException se directory output non configurata
     * @throws RuntimeException se errori durante generazione file
     */
    public void generateInstances(int numberOfProblems) {
        // Fase 1: Validazione e inizializzazione
        if (!initializeGeneration(numberOfProblems)) {
            return; // Terminazione anticipata per errori configurazione
        }

        try {
            // Fase 2: Preparazione ambiente output
            setupOutputEnvironment();

            // Fase 3: Generazione sequenziale istanze
            executeInstanceGeneration(numberOfProblems);

            // Fase 4: Finalizzazione e report
            finalizeGenerationWithReport(numberOfProblems);

        } catch (Exception e) {
            handleGenerationError(e, numberOfProblems);
        }
    }

    //endregion

    //region INIZIALIZZAZIONE E VALIDAZIONE

    /**
     * Inizializza processo di generazione con validazione completa dell'input.
     *
     * @param numberOfProblems numero istanze richieste
     * @return true se inizializzazione successful, false se errori rilevati
     */
    private boolean initializeGeneration(int numberOfProblems) {
        // NON resettare se la directory è già configurata
        if (outputDirectory == null) {
            resetGenerationState();
        } else {
            // Reset parziale mantenendo outputDirectory
            generatedInstances = 0;
            generationLog = new StringBuilder();
        }

        generationLog.append("=== INIZIO GENERAZIONE PIGEONHOLE PROBLEM ===\n");

        // Validazione numero problemi
        if (numberOfProblems < 1 || numberOfProblems > 100) {
            String error = "Numero problemi deve essere tra 1 e 100, ricevuto: " + numberOfProblems;
            LOGGER.warning(error);
            generationLog.append("ERRORE: ").append(error).append("\n");
            return false;
        }

        // Validazione directory output
        if (outputDirectory == null) {
            String error = "Directory output non configurata - chiamare setOutputDirectory() prima";
            LOGGER.warning(error);
            generationLog.append("ERRORE: ").append(error).append("\n");
            return false;
        }

        generationLog.append("Numero istanze richieste: ").append(numberOfProblems).append("\n");
        generationLog.append("Directory base: ").append(outputDirectory).append("\n\n");

        LOGGER.info("Inizio generazione " + numberOfProblems + " istanze Pigeonhole Problem");
        return true;
    }

    /**
     * Prepara l'ambiente di output creando directory necessarie.
     */
    private void setupOutputEnvironment() throws IOException {
        // Crea directory base se non esiste
        Path basePath = Paths.get(outputDirectory);
        Files.createDirectories(basePath);

        // Crea sottodirectory PIGEONHOLE
        Path pigeonholePath = basePath.resolve(PIGEONHOLE_DIR);
        Files.createDirectories(pigeonholePath);

        generationLog.append("Directory PIGEONHOLE creata: ").append(pigeonholePath).append("\n");
        LOGGER.fine("Directory output preparata: " + pigeonholePath);
    }

    /**
     * Gestisce errori durante generazione con logging completo.
     */
    private void handleGenerationError(Exception e, int numberOfProblems) {
        LOGGER.log(Level.SEVERE, "Errore durante generazione istanze Pigeonhole", e);
        generationLog.append("ERRORE CRITICO: ").append(e.getMessage()).append("\n");

        System.out.println("[E] Generazione fallita dopo " + generatedInstances + "/" + numberOfProblems + " istanze");
        System.out.println("[E] Errore: " + e.getMessage());

        throw new RuntimeException("Generazione istanze Pigeonhole fallita", e);
    }

    //endregion

    //region GENERAZIONE SEQUENZIALE ISTANZE

    /**
     * Esegue generazione sequenziale di tutte le istanze richieste.
     *
     * @param numberOfProblems numero totale istanze da generare
     */
    private void executeInstanceGeneration(int numberOfProblems) throws IOException {
        generationLog.append("=== GENERAZIONE SEQUENZIALE ISTANZE ===\n");

        for (int n = 1; n <= numberOfProblems; n++) {
            LOGGER.fine("Generazione istanza " + n + "/" + numberOfProblems);
            generateSingleInstance(n);
            generatedInstances++;

            // Log progresso ogni 10 istanze
            if (n % 10 == 0) {
                System.out.println("[I] Progresso generazione: " + n + "/" + numberOfProblems + " istanze completate");
            }
        }
    }

    /**
     * Genera singola istanza del Pigeonhole Problem per dimensione specifica.
     *
     * FORMULAZIONE MATEMATICA:
     * - n buche, n+1 piccioni
     * - Variabili: p_ij = "piccione i è nella buca j"
     * - Vincoli positivi: ∀i ∈ [1,n+1]: (p_i1 ∨ p_i2 ∨ ... ∨ p_in)
     * - Vincoli negativi: ∀j ∈ [1,n], ∀(i,h) ∈ C²_n+1: (¬p_ij ∨ ¬p_hj)
     *
     * @param n dimensione problema (numero buche)
     */
    private void generateSingleInstance(int n) throws IOException {
        generationLog.append("Generazione istanza n=").append(n).append(" (")
                .append(n + 1).append(" piccioni, ").append(n).append(" buche)\n");

        // Costruisce formula completa
        PigeonholeFormula formula = buildPigeonholeFormula(n);

        // Salva su file
        savePigeonholeInstance(formula, n);

        generationLog.append("Istanza n=").append(n).append(" completata: ")
                .append(formula.getTotalClauses()).append(" clausole, ")
                .append(formula.getTotalVariables()).append(" variabili\n");
    }

    /**
     * Costruisce formula logica completa per Pigeonhole Problem dimensione n.
     *
     * @param n dimensione problema (numero buche)
     * @return formula strutturata pronta per salvataggio
     */
    private PigeonholeFormula buildPigeonholeFormula(int n) {
        PigeonholeFormula formula = new PigeonholeFormula(n);

        // PARTE 1: Vincoli positivi - ogni piccione in almeno una buca
        generatePositiveConstraints(formula, n);

        // PARTE 2: Vincoli negativi - ogni buca al più un piccione
        generateNegativeConstraints(formula, n);

        return formula;
    }

    /**
     * Genera vincoli positivi: ogni piccione deve essere in almeno una buca.
     *
     * ∀i ∈ [1,n+1]: (p_i1 ∨ p_i2 ∨ ... ∨ p_in)
     *
     * @param formula contenitore formula da popolare
     * @param n dimensione problema
     */
    private void generatePositiveConstraints(PigeonholeFormula formula, int n) {
        for (int pigeon = 1; pigeon <= n + 1; pigeon++) {
            List<String> clause = new ArrayList<>();

            // Piccione i può essere in qualsiasi buca j
            for (int hole = 1; hole <= n; hole++) {
                clause.add("p" + pigeon + hole);
            }

            formula.addClause(clause);
        }
    }

    /**
     * Genera vincoli negativi: ogni buca può contenere al più un piccione.
     *
     * ∀j ∈ [1,n], ∀(i,h) ∈ C²_n+1: (¬p_ij ∨ ¬p_hj)
     *
     * @param formula contenitore formula da popolare
     * @param n dimensione problema
     */
    private void generateNegativeConstraints(PigeonholeFormula formula, int n) {
        for (int hole = 1; hole <= n; hole++) {
            // Per ogni coppia di piccioni diversi nella stessa buca
            for (int pigeon1 = 1; pigeon1 <= n + 1; pigeon1++) {
                for (int pigeon2 = pigeon1 + 1; pigeon2 <= n + 1; pigeon2++) {
                    List<String> clause = new ArrayList<>();
                    clause.add("!p" + pigeon1 + hole);  // ¬p_ij
                    clause.add("!p" + pigeon2 + hole);  // ¬p_hj
                    formula.addClause(clause);
                }
            }
        }
    }

    //endregion

    //region SALVATAGGIO FILE

    /**
     * Salva istanza Pigeonhole Problem su file con formato parser-compatible.
     *
     * @param formula formula logica da salvare
     * @param n dimensione problema per naming file
     */
    private void savePigeonholeInstance(PigeonholeFormula formula, int n) throws IOException {
        // Costruisce percorso file output
        Path basePath = Paths.get(outputDirectory);
        Path pigeonholePath = basePath.resolve(PIGEONHOLE_DIR);
        String fileName = FILE_PREFIX + n + FILE_EXTENSION;
        Path filePath = pigeonholePath.resolve(fileName);

        // Scrive formula su file
        try (FileWriter writer = new FileWriter(filePath.toFile())) {
            writeFormulaToFile(writer, formula, n);
        }

        generationLog.append("File salvato: ").append(filePath).append("\n");
        LOGGER.finest("Istanza n=" + n + " salvata: " + filePath);
    }

    /**
     * Scrive formula formattata nel file di output.
     *
     * FORMATO OUTPUT:
     * - Ogni clausola racchiusa tra parentesi tonde
     * - OR rappresentato con |
     * - AND rappresentato con &
     * - NOT rappresentato con !
     *
     * @param writer stream di scrittura file
     * @param formula formula da scrivere
     * @param n dimensione problema per header
     */
    private void writeFormulaToFile(FileWriter writer, PigeonholeFormula formula, int n) throws IOException {
        // Formula in formato CNF con parentesi
        List<String> clauses = formula.getFormattedClauses();
        for (int i = 0; i < clauses.size(); i++) {
            writer.write(clauses.get(i));

            if (i < clauses.size() - 1) {
                writer.write(" & ");  // AND tra clausole
            }
        }

        writer.write("\n");
    }

    //endregion

    //region FINALIZZAZIONE E REPORTING

    /**
     * Finalizza generazione con report completo delle istanze create.
     */
    private void finalizeGenerationWithReport(int numberOfProblems) {
        generationLog.append("\n=== GENERAZIONE COMPLETATA ===\n");
        generationLog.append("Istanze generate: ").append(generatedInstances).append("/").append(numberOfProblems).append("\n");
        generationLog.append("Directory output: ").append(Paths.get(outputDirectory).resolve(PIGEONHOLE_DIR)).append("\n");

        // Calcola statistiche aggregate
        generateAggregateStatistics(numberOfProblems);

        LOGGER.info("Generazione completata: " + generatedInstances + " istanze create");
        System.out.println("[I] Generazione Pigeonhole Problem completata!");
        System.out.println("[I] Istanze create: " + generatedInstances + "/" + numberOfProblems);
        System.out.println("[I] Directory: " + Paths.get(outputDirectory).resolve(PIGEONHOLE_DIR));
    }

    /**
     * Genera statistiche aggregate per tutte le istanze create.
     */
    private void generateAggregateStatistics(int numberOfProblems) {
        generationLog.append("\n=== STATISTICHE AGGREGATE ===\n");

        int totalClauses = 0;
        int totalVariables = 0;

        for (int n = 1; n <= numberOfProblems; n++) {
            // Calcola statistiche per dimensione n
            int clausesForN = calculateClausesForDimension(n);
            int variablesForN = calculateVariablesForDimension(n);

            totalClauses += clausesForN;
            totalVariables += Math.max(totalVariables, variablesForN); // Variabili distinte cumulative

            generationLog.append("n=").append(n).append(": ")
                    .append(clausesForN).append(" clausole, ")
                    .append(variablesForN).append(" variabili\n");
        }

        generationLog.append("\nTotale clausole aggregate: ").append(totalClauses).append("\n");
        generationLog.append("Complessità massima (n=").append(numberOfProblems).append("): ")
                .append(calculateVariablesForDimension(numberOfProblems)).append(" variabili, ")
                .append(calculateClausesForDimension(numberOfProblems)).append(" clausole\n");
    }

    /**
     * Calcola numero di clausole per problema dimensione n.
     * Formula: (n+1) + C(n+1,2) × n = (n+1) + n×(n+1)×n/2
     */
    private int calculateClausesForDimension(int n) {
        int positiveConstraints = n + 1;                    // Una per ogni piccione
        int negativeConstraints = n * (n + 1) * n / 2;      // Combinazioni per ogni buca
        return positiveConstraints + negativeConstraints;
    }

    /**
     * Calcola numero di variabili per problema dimensione n.
     * Formula: (n+1) × n variabili p_ij
     */
    private int calculateVariablesForDimension(int n) {
        return (n + 1) * n;
    }

    //endregion

    //region INTERFACCIA PUBBLICA INFORMAZIONI

    /**
     * Restituisce report dettagliato della generazione per output utente.
     *
     * @return stringa formattata con statistiche e dettagli completi
     */
    public String getGenerationReport() {
        return generationLog.toString();
    }

    /**
     * @return numero istanze generate nella sessione corrente
     */
    public int getGeneratedInstancesCount() {
        return generatedInstances;
    }

    /**
     * @return directory output configurata correntemente
     */
    public String getOutputDirectory() {
        return outputDirectory;
    }

    /**
     * Reset per nuovo utilizzo del generatore.
     */
    public void reset() {
        resetGenerationState();
        LOGGER.fine("PigeonholeProblem resettato per nuovo utilizzo");
    }

    /**
     * Rappresentazione testuale del generatore per debugging.
     */
    @Override
    public String toString() {
        return String.format("PigeonholeProblem[generated=%d, output=%s]",
                generatedInstances, outputDirectory);
    }

    //endregion

    //region CLASSE FORMULA STRUTTURATA

    /**
     * FORMULA PIGEONHOLE - Contenitore strutturato per formula logica
     *
     * Rappresenta una singola istanza del Pigeonhole Problem con tutte le
     * clausole generate e metodi di formattazione per output compatibile.
     */
    private static class PigeonholeFormula {
        private final int dimension;                        // Dimensione problema (n)
        private final List<List<String>> clauses;          // Clausole della formula
        private final int totalVariables;                  // Numero variabili distinte

        /**
         * Costruisce contenitore vuoto per formula dimensione n.
         */
        public PigeonholeFormula(int n) {
            this.dimension = n;
            this.clauses = new ArrayList<>();
            this.totalVariables = (n + 1) * n;             // p_ij per i∈[1,n+1], j∈[1,n]
        }

        /**
         * Aggiunge clausola alla formula.
         */
        public void addClause(List<String> clause) {
            clauses.add(new ArrayList<>(clause));          // Copia difensiva
        }

        /**
         * Restituisce clausole formattate per output file.
         */
        public List<String> getFormattedClauses() {
            List<String> formatted = new ArrayList<>();
            for (List<String> clause : clauses) {
                formatted.add(formatSingleClause(clause));
            }
            return formatted;
        }

        /**
         * Formatta singola clausola con parentesi e separatori OR.
         */
        private String formatSingleClause(List<String> clause) {
            return "(" + String.join(" | ", clause) + ")";
        }

        public int getTotalClauses() { return clauses.size(); }
        public int getTotalVariables() { return totalVariables; }
        public int getDimension() { return dimension; }
    }

    //endregion
}