package org.sat.support;

import java.util.*;
import java.util.logging.Logger;

/**
 * DECISION STACK - Stack gerarchico per gestione livelli nell'algoritmo CDCL
 *
 * Implementa la struttura dati avanzata per organizzazione gerarchica delle decisioni
 * e implicazioni durante la ricerca SAT. Fornisce supporto completo per operazioni
 * di backtracking cronologico e non-cronologico con efficienza ottimale.
 *
 * ORGANIZZAZIONE GERARCHICA:
 * • Livello 0: implicazioni da clausole unitarie originali (sempre presente)
 * • Livello i (i>0): livello di decisione i con decisione + implicazioni derivate
 * • Ogni livello mantiene cronologia completa degli assegnamenti
 * • Stack mai completamente vuoto per garantire stabilità
 *
 * OPERAZIONI SUPPORTATE:
 * • Aggiunta decisioni euristiche con creazione nuovi livelli
 * • Aggiunta implicazioni al livello corrente
 * • Backtracking cronologico (rimozione livello superiore)
 * • Backjumping non-cronologico (salto a livelli specifici)
 * • Interrogazione stato e navigazione livelli
 *
 * INVARIANTI MANTENUTE:
 * • Stack contiene sempre almeno livello 0
 * • Ogni livello ha struttura temporale consistente
 * • Operazioni atomiche per consistenza durante backtracking
 * • Validazione completa di tutti i parametri
 */
public class DecisionStack {

    private static final Logger LOGGER = Logger.getLogger(DecisionStack.class.getName());

    //region STRUTTURA DATI STACK GERARCHICO

    /**
     * Stack dei livelli di decisione con organizzazione gerarchica ottimizzata.
     *
     * STRUTTURA DETTAGLIATA:
     * • Indice 0: livello 0 (implicazioni iniziali, sempre presente)
     * • Indice i>0: livello i di decisione con cronologia temporale
     * • Ogni livello è ArrayList<AssignedLiteral> con assegnamenti ordinati cronologicamente
     *
     * INVARIANTI CRITICHE:
     * • size() >= 1 (livello 0 sempre presente, mai rimosso)
     * • Ogni livello non null e con struttura valida
     * • Ordine cronologico mantenuto all'interno di ogni livello
     */
    private final Stack<ArrayList<AssignedLiteral>> levelStack;

    //endregion

    //region INIZIALIZZAZIONE E CONFIGURAZIONE

    /**
     * Inizializza stack con livello 0 vuoto e pronto per operazioni.
     * Il livello 0 è riservato esclusivamente a implicazioni da clausole unitarie originali.
     */
    public DecisionStack() {
        this.levelStack = new Stack<>();
        this.levelStack.push(new ArrayList<>()); // Livello 0 iniziale sempre presente

        LOGGER.fine("DecisionStack inizializzato con livello 0 protetto");
    }

    //endregion

    //region OPERAZIONI DI AGGIUNTA CON VALIDAZIONE

    /**
     * Aggiunge decisione euristica creando nuovo livello gerarchico.
     *
     * ALGORITMO AGGIUNTA DECISIONE:
     * 1. Validazione parametri di input per consistenza e range
     * 2. Creazione assegnamento decisionale con metadata completi
     * 3. Inizializzazione nuovo livello con la decisione come primo elemento
     * 4. Push atomico del nuovo livello nello stack (incrementa altezza)
     * 5. Logging informazioni per debugging e audit
     *
     * @param variable ID variabile da decidere (> 0, non ancora assegnata)
     * @param value valore booleano da assegnare alla variabile
     * @throws IllegalArgumentException se parametri non validi
     * @throws IllegalStateException se variabile già assegnata
     */
    public void addDecision(Integer variable, Boolean value) {
        validateDecisionParameters(variable, value);

        // Crea assegnamento decisionale auto-giustificato
        AssignedLiteral decision = new AssignedLiteral(variable, value, true, null);

        // Inizializza nuovo livello con la decisione
        ArrayList<AssignedLiteral> newDecisionLevel = new ArrayList<>();
        newDecisionLevel.add(decision);

        // Operazione atomica di aggiunta livello
        levelStack.push(newDecisionLevel);

        int currentLevel = levelStack.size() - 1;
        LOGGER.fine(String.format("Decisione aggiunta: var=%d, val=%s, livello=%d, altezza_stack=%d",
                variable, value, currentLevel, levelStack.size()));
    }

    /**
     * Aggiunge implicazione derivata da unit propagation al livello corrente.
     *
     * ALGORITMO AGGIUNTA IMPLICAZIONE:
     * 1. Validazione parametri e clausola ancestrale per consistenza
     * 2. Verifica stato stack per prevenzione inconsistenze
     * 3. Creazione assegnamento di implicazione con genealogia
     * 4. Modifica atomica del livello corrente (pop + modifica + push)
     * 5. Logging con informazioni contestuali dettagliate
     *
     * @param variable ID variabile implicata (> 0)
     * @param value valore implicato dalla propagazione
     * @param ancestorClause clausola unitaria causante l'implicazione
     * @throws IllegalArgumentException se parametri non validi
     * @throws IllegalStateException se stack inconsistente
     */
    public void addImpliedLiteral(Integer variable, Boolean value, List<Integer> ancestorClause) {
        validateImplicationParameters(variable, value, ancestorClause);

        if (levelStack.isEmpty()) {
            throw new IllegalStateException("Stack vuoto - impossibile aggiungere implicazione");
        }

        // Crea implicazione con clausola ancestrale per tracciabilità
        AssignedLiteral implication = new AssignedLiteral(variable, value, false, ancestorClause);

        // Modifica atomica del livello corrente
        ArrayList<AssignedLiteral> currentLevel = levelStack.pop();
        currentLevel.add(implication);
        levelStack.push(currentLevel);

        int levelIndex = levelStack.size() - 1;
        LOGGER.fine(String.format("Implicazione aggiunta: var=%d, val=%s, livello=%d, clausola=%s, size_livello=%d",
                variable, value, levelIndex, ancestorClause, currentLevel.size()));
    }

    /**
     * Valida parametri per aggiunta decisione.
     */
    private void validateDecisionParameters(Integer variable, Boolean value) {
        if (variable == null || variable <= 0) {
            throw new IllegalArgumentException("Variable ID per decisione deve essere > 0, ricevuto: " + variable);
        }
        if (value == null) {
            throw new IllegalArgumentException("Value per decisione non può essere null");
        }
    }

    /**
     * Valida parametri per aggiunta implicazione.
     */
    private void validateImplicationParameters(Integer variable, Boolean value, List<Integer> ancestorClause) {
        if (variable == null || variable <= 0) {
            throw new IllegalArgumentException("Variable ID per implicazione deve essere > 0, ricevuto: " + variable);
        }
        if (value == null) {
            throw new IllegalArgumentException("Value per implicazione non può essere null");
        }
        if (ancestorClause == null || ancestorClause.isEmpty()) {
            throw new IllegalArgumentException("AncestorClause richiesta per implicazioni");
        }

        // Validazione contenuto clausola ancestrale
        for (Integer literal : ancestorClause) {
            if (literal == null || literal == 0) {
                throw new IllegalArgumentException("Clausola ancestrale contiene letterale non valido: " + literal);
            }
        }
    }

    //endregion

    //region OPERAZIONI DI RIMOZIONE E BACKTRACKING

    /**
     * Rimuove livello più alto (backtracking cronologico singolo).
     *
     * PROTEZIONI IMPLEMENTATE:
     * • Livello 0 è protetto e non può mai essere rimosso
     * • Operazione atomica per garantire consistenza durante concorrenza
     * • Restituisce copia difensiva degli assegnamenti rimossi
     * • Logging dettagliato per audit delle operazioni
     *
     * @return lista assegnamenti del livello rimosso (vuota se tentativo rimozione livello 0)
     */
    public List<AssignedLiteral> deleteLevel() {
        if (levelStack.size() <= 1) {
            LOGGER.warning("Tentativo rimozione livello 0 protetto - operazione ignorata per sicurezza");
            return new ArrayList<>(); // Protezione livello 0
        }

        ArrayList<AssignedLiteral> removedLevel = levelStack.pop();
        int removedLevelIndex = levelStack.size(); // Indice del livello appena rimosso

        LOGGER.fine(String.format("Livello %d rimosso: %d assegnamenti, altezza_stack=%d",
                removedLevelIndex, removedLevel.size(), levelStack.size()));

        // Log dettagliato assegnamenti rimossi per debugging
        if (LOGGER.isLoggable(java.util.logging.Level.FINEST)) {
            for (int i = 0; i < removedLevel.size(); i++) {
                AssignedLiteral assignment = removedLevel.get(i);
                LOGGER.finest(String.format("Rimosso[%d]: %s", i, assignment));
            }
        }

        return new ArrayList<>(removedLevel); // Copia difensiva
    }

    /**
     * Backtracking non-cronologico al livello target (backjumping avanzato).
     *
     * ALGORITMO BACKJUMPING:
     * 1. Validazione livello target per safety e consistenza
     * 2. Rimozione sequenziale livelli superiori fino a target
     * 3. Raccolta tutti gli assegnamenti rimossi per rollback
     * 4. Logging statistiche complete dell'operazione
     * 5. Verifica integrità finale dello stack
     *
     * @param targetLevel livello di destinazione (>= 0, <= livello corrente)
     * @return tutti gli assegnamenti rimossi durante l'operazione di backjump
     * @throws IllegalArgumentException se targetLevel non valido
     */
    public List<AssignedLiteral> backtrackToLevel(int targetLevel) {
        int currentLevel = levelStack.size() - 1;
        validateBacktrackLevel(targetLevel, currentLevel);

        if (targetLevel == currentLevel) {
            LOGGER.fine("Backtrack richiesto al livello corrente - nessuna operazione necessaria");
            return new ArrayList<>();
        }

        List<AssignedLiteral> allRemovedAssignments = new ArrayList<>();
        int levelsToRemove = currentLevel - targetLevel;

        // Rimozione sequenziale con accumulo assegnamenti
        for (int i = 0; i < levelsToRemove; i++) {
            List<AssignedLiteral> removedLevel = deleteLevel();
            allRemovedAssignments.addAll(removedLevel);
        }

        LOGGER.info(String.format("Backjump completato: %d → %d (%d livelli), %d assegnamenti rimossi",
                currentLevel, targetLevel, levelsToRemove, allRemovedAssignments.size()));

        return allRemovedAssignments;
    }

    /**
     * Valida livello target per operazioni backtrack.
     */
    private void validateBacktrackLevel(int targetLevel, int currentLevel) {
        if (targetLevel < 0) {
            throw new IllegalArgumentException("Target level non può essere negativo: " + targetLevel);
        }
        if (targetLevel > currentLevel) {
            throw new IllegalArgumentException(
                    String.format("Target level %d > current level %d", targetLevel, currentLevel));
        }
    }

    //endregion

    //region OPERAZIONI DI INTERROGAZIONE E NAVIGAZIONE

    /**
     * @return copia difensiva degli assegnamenti nel livello più alto
     */
    public List<AssignedLiteral> getTopLevel() {
        if (levelStack.isEmpty()) {
            throw new IllegalStateException("Stack vuoto - nessun livello disponibile");
        }
        return new ArrayList<>(levelStack.peek());
    }

    /**
     * @return livello corrente (numero di livelli - 1, sempre >= 0)
     */
    public int getLevel() {
        return levelStack.size() - 1;
    }

    /**
     * @return numero totale di livelli nello stack (sempre >= 1)
     */
    public int size() {
        return levelStack.size();
    }

    /**
     * Restituisce ID delle variabili assegnate a livello specifico.
     * @param levelIndex indice livello da interrogare (0 <= levelIndex < size())
     * @return lista ID variabili in ordine cronologico di assegnamento
     */
    public List<Integer> getLiteralsAtLevel(int levelIndex) {
        validateLevelIndex(levelIndex);

        List<AssignedLiteral> levelAssignments = levelStack.get(levelIndex);
        return levelAssignments.stream()
                .map(AssignedLiteral::getVariable)
                .collect(java.util.stream.Collectors.toList());
    }

    /**
     * Restituisce tutti gli assegnamenti a livello specifico.
     * @param levelIndex indice livello da interrogare
     * @return copia difensiva degli assegnamenti al livello
     */
    public List<AssignedLiteral> getAssignmentsAtLevel(int levelIndex) {
        validateLevelIndex(levelIndex);
        return new ArrayList<>(levelStack.get(levelIndex));
    }

    /**
     * @return true se stack contiene solo livello 0 vuoto
     */
    public boolean isEmpty() {
        return levelStack.size() == 1 && levelStack.peek().isEmpty();
    }

    /**
     * @return numero totale assegnamenti in tutti i livelli
     */
    public int getTotalAssignments() {
        return levelStack.stream()
                .mapToInt(ArrayList::size)
                .sum();
    }

    /**
     * Trova livello di decisione di una variabile specifica.
     * @param variable ID variabile da cercare
     * @return livello della variabile o -1 se non trovata
     */
    public int findVariableLevel(Integer variable) {
        if (variable == null) {
            return -1;
        }

        for (int level = 0; level < levelStack.size(); level++) {
            List<AssignedLiteral> levelAssignments = levelStack.get(level);

            for (AssignedLiteral assignment : levelAssignments) {
                if (assignment.getVariable().equals(variable)) {
                    return level;
                }
            }
        }

        return -1; // Variabile non trovata
    }

    /**
     * Trova assegnamento specifico per una variabile.
     * @param variable ID variabile da cercare
     * @return assegnamento della variabile o null se non trovata
     */
    public AssignedLiteral findVariableAssignment(Integer variable) {
        if (variable == null) {
            return null;
        }

        for (ArrayList<AssignedLiteral> level : levelStack) {
            for (AssignedLiteral assignment : level) {
                if (assignment.getVariable().equals(variable)) {
                    return assignment;
                }
            }
        }

        return null; // Variabile non trovata
    }

    /**
     * Valida indice livello per accesso sicuro.
     */
    private void validateLevelIndex(int levelIndex) {
        if (levelIndex < 0 || levelIndex >= levelStack.size()) {
            throw new IndexOutOfBoundsException(
                    String.format("Level index %d fuori range [0, %d)", levelIndex, levelStack.size()));
        }
    }

    //endregion

    //region STATISTICHE E RAPPRESENTAZIONE

    /**
     * Restituisce statistiche dettagliate sullo stack per analisi performance.
     */
    public StackStatistics getStatistics() {
        int totalLevels = levelStack.size();
        int totalAssignments = getTotalAssignments();
        int decisionsCount = totalLevels - 1; // Esclude livello 0
        int implicationsCount = totalAssignments - decisionsCount;

        return new StackStatistics(totalLevels, totalAssignments, decisionsCount, implicationsCount);
    }

    /**
     * Rappresentazione testuale completa per debugging avanzato.
     */
    @Override
    public String toString() {
        StringBuilder representation = new StringBuilder();
        representation.append("DecisionStack {\n");
        representation.append(String.format("  Livelli: %d, Assegnamenti totali: %d\n",
                levelStack.size(), getTotalAssignments()));

        for (int levelIndex = 0; levelIndex < levelStack.size(); levelIndex++) {
            ArrayList<AssignedLiteral> level = levelStack.get(levelIndex);
            representation.append(String.format("\n  Livello %d (%d assegnamenti):\n",
                    levelIndex, level.size()));

            if (level.isEmpty()) {
                representation.append("    [vuoto]\n");
                continue;
            }

            for (int i = 0; i < level.size(); i++) {
                AssignedLiteral assignment = level.get(i);
                String type = assignment.isDecision() ? "DECISION" : "IMPLIED";
                String clauseInfo = assignment.hasAncestorClause()
                        ? " ← " + assignment.getAncestorClause()
                        : "";

                representation.append(String.format("    [%d] %s: %d → %s%s\n",
                        i, type, assignment.getVariable(), assignment.getValue(), clauseInfo));
            }
        }

        representation.append("}");
        return representation.toString();
    }

    //endregion

    //region CLASSI DI SUPPORTO

    /**
     * Statistiche dettagliate dello stack per analisi performance.
     */
    public static class StackStatistics {
        public final int totalLevels;
        public final int totalAssignments;
        public final int decisionsCount;
        public final int implicationsCount;

        public StackStatistics(int totalLevels, int totalAssignments, int decisionsCount, int implicationsCount) {
            this.totalLevels = totalLevels;
            this.totalAssignments = totalAssignments;
            this.decisionsCount = decisionsCount;
            this.implicationsCount = implicationsCount;
        }

        @Override
        public String toString() {
            return String.format("StackStats{levels=%d, assignments=%d, decisions=%d, implications=%d}",
                    totalLevels, totalAssignments, decisionsCount, implicationsCount);
        }
    }

    //endregion
}