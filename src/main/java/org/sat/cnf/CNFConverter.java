package org.sat.cnf;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.logging.Logger;
import java.util.logging.Level;

/**
 * Sistema completo per rappresentazione e trasformazione formule logiche
 *
 * Rappresenta formule logiche proposizionali in forma ad albero e implementa la loro
 * trasformazione in Forma Normale Congiuntiva (CNF), applicando algoritmi matematici
 * rigorosi per preservare equivalenza logica durante tutte le trasformazioni.
 *
 */
public class CNFConverter {

    private static final Logger LOGGER = Logger.getLogger(CNFConverter.class.getName());

    //region TIPI E STRUTTURA DATI

    /**
     * Tipi di nodi supportati nella rappresentazione ad albero.
     * Coprono tutti gli operatori della logica proposizionale standard.
     */
    public enum Type {
        AND,    // Congiunzione: A & B
        OR,     // Disgiunzione: A | B
        NOT,    // Negazione: !A
        ATOM    // Variabile atomica: P, Q, R, ...
    }

    /** Tipo del nodo corrente nell'albero */
    public Type type;

    /** Nome della variabile atomica (solo per nodi ATOM) */
    public String atom;

    /** Operando singolo (solo per nodi NOT) */
    public CNFConverter operand;

    /** Lista operandi (solo per nodi AND e OR) */
    public List<CNFConverter> operands;

    //endregion

    //region COSTRUTTORI E INIZIALIZZAZIONE

    /**
     * Costruisce nodo foglia per variabile atomica.
     *
     * @param atom nome della variabile proposizionale (non null, non vuoto)
     * @throws IllegalArgumentException se atom null o vuoto
     */
    public CNFConverter(String atom) {
        if (atom == null || atom.trim().isEmpty()) {
            throw new IllegalArgumentException("Nome variabile atomica non può essere null o vuoto");
        }

        this.type = Type.ATOM;
        this.atom = atom.trim();
    }

    /**
     * Costruisce nodo unario per operazione NOT.
     *
     * @param operand sottostruttura da negare (non null)
     * @throws IllegalArgumentException se operand null
     */
    public CNFConverter(CNFConverter operand) {
        if (operand == null) {
            throw new IllegalArgumentException("Operando per negazione non può essere null");
        }

        this.type = Type.NOT;
        this.operand = operand;
    }

    /**
     * Costruisce nodo binario/n-ario per operazioni AND e OR.
     *
     * @param type tipo di operazione (AND o OR)
     * @param operands lista operandi (non null, non vuota)
     * @throws IllegalArgumentException se parametri non validi
     */
    public CNFConverter(Type type, List<CNFConverter> operands) {
        if (type != Type.AND && type != Type.OR) {
            throw new IllegalArgumentException("Tipo deve essere AND o OR per operazioni multiple");
        }
        if (operands == null || operands.isEmpty()) {
            throw new IllegalArgumentException("Lista operandi non può essere null o vuota");
        }
        if (operands.contains(null)) {
            throw new IllegalArgumentException("Lista operandi non può contenere elementi null");
        }

        this.type = type;
        this.operands = new ArrayList<>(operands); // Copia difensiva
    }

    //endregion

    //region INTERFACCIA PUBBLICA CONVERSIONE CNF

    /**
     * METODO PRINCIPALE - Converte la formula in Forma Normale Congiuntiva (CNF)
     *
     * Applica sequenzialmente tutte le trasformazioni matematiche necessarie per
     * ottenere una formula logicamente equivalente in CNF, preservando semantica.
     *
     * PIPELINE TRASFORMAZIONE:
     * 1. Eliminazione implicazioni e biimplicazioni (se presenti)
     * 2. Normalizzazione negazioni con leggi di De Morgan
     * 3. Distribuzione OR su AND per forma canonica
     * 4. Semplificazione strutturale per ottimizzazione
     *
     * @return formula in CNF logicamente equivalente all'originale
     * @throws RuntimeException se errori durante trasformazione
     */
    public CNFConverter toCNF() {
        try {
            CNFConverter result = this;
            LOGGER.fine("Inizio conversione CNF per: " + result);

            // Fase 1: Normalizzazione negazioni (leggi di De Morgan)
            result = result.normalizeNegations();
            LOGGER.finest("Dopo normalizzazione negazioni: " + result);

            // Fase 2: Distribuzione OR su AND (forma canonica)
            result = result.distributeOrOverAnd();
            LOGGER.finest("Dopo distribuzione OR su AND: " + result);

            // Fase 3: Semplificazione strutturale finale
            result = result.simplifyStructure();
            LOGGER.fine("Conversione CNF completata: " + result);

            return result;

        } catch (Exception e) {
            LOGGER.log(Level.SEVERE, "Errore durante conversione CNF", e);
            throw new RuntimeException("Conversione CNF fallita per formula: " + this, e);
        }
    }

    //endregion

    //region NORMALIZZAZIONE NEGAZIONI (LEGGI DE MORGAN)

    /**
     * Normalizza le negazioni spingendole verso le foglie usando le leggi di De Morgan.
     *
     * TRASFORMAZIONI APPLICATE:
     * • !(A | B) -> !A & !B
     * • !(A & B) -> !A | !B
     * • !!A -> A
     * • Negazioni atomiche preservate: !P rimane !P
     *
     * @return formula con negazioni normalizzate
     */
    private CNFConverter normalizeNegations() {
        return switch (this.type) {
            case ATOM -> this; // Caso base: atomi invariati

            case NOT -> applyNegationTransformation();

            case OR -> {
                // Normalizza ricorsivamente tutti gli operandi OR
                List<CNFConverter> normalizedOperands = new ArrayList<>();
                for (CNFConverter operand : operands) {
                    normalizedOperands.add(operand.normalizeNegations());
                }
                yield new CNFConverter(Type.OR, normalizedOperands);
            }

            case AND -> {
                // Normalizza ricorsivamente tutti gli operandi AND
                List<CNFConverter> normalizedOperands = new ArrayList<>();
                for (CNFConverter operand : operands) {
                    normalizedOperands.add(operand.normalizeNegations());
                }
                yield new CNFConverter(Type.AND, normalizedOperands);
            }
        };
    }

    /**
     * Applica trasformazioni specifiche per negazioni usando leggi di De Morgan.
     */
    private CNFConverter applyNegationTransformation() {
        CNFConverter innerFormula = operand.normalizeNegations();

        return switch (innerFormula.type) {
            case ATOM ->
                // !A rimane !A (forma normale per letterali)
                    new CNFConverter(innerFormula);

            case NOT ->
                // !!A -> A (eliminazione doppia negazione)
                    innerFormula.operand;

            case AND -> {
                // !(A & B & C) -> !A | !B | !C (De Morgan per congiunzioni)
                List<CNFConverter> negatedOperands = new ArrayList<>();
                for (CNFConverter operand : innerFormula.operands) {
                    negatedOperands.add(new CNFConverter(operand));
                }
                yield new CNFConverter(Type.OR, negatedOperands);
            }

            case OR -> {
                // !(A | B | C) -> !A & !B & !C (De Morgan per disgiunzioni)
                List<CNFConverter> negatedOperands = new ArrayList<>();
                for (CNFConverter operand : innerFormula.operands) {
                    negatedOperands.add(new CNFConverter(operand));
                }
                yield new CNFConverter(Type.AND, negatedOperands);
            }
        };
    }

    //endregion

    //region DISTRIBUZIONE OR SU AND (FORMA CANONICA)

    /**
     * Distribuisce OR sopra AND per ottenere forma canonica CNF.
     *
     * PROPRIETÀ DISTRIBUTIVA APPLICATA:
     * • A | (B & C) -> (A | B) & (A | C)
     * • (A & B) | C -> (A | C) & (B | C)
     * • (A & B) | (C & D) -> (A | C) & (A | D) & (B | C) & (B | D)
     *
     * @return formula in forma CNF canonica
     */
    private CNFConverter distributeOrOverAnd() {
        return switch (this.type) {
            case ATOM -> this; // Caso base: atomi invariati

            case NOT -> {
                // Verifica che negazioni siano solo su atomi (post-normalizzazione)
                if (operand.type == Type.ATOM) {
                    yield this;
                } else {
                    // Dovrebbe essere già risolto da normalizeNegations
                    LOGGER.warning("Negazione non atomica trovata durante distribuzione: " + this);
                    CNFConverter normalized = this.normalizeNegations();
                    yield normalized.distributeOrOverAnd();
                }
            }

            case AND -> {
                // Distribuisce ricorsivamente su tutti gli operandi AND
                List<CNFConverter> distributedOperands = new ArrayList<>();
                for (CNFConverter operand : operands) {
                    distributedOperands.add(operand.distributeOrOverAnd());
                }
                yield new CNFConverter(Type.AND, distributedOperands);
            }

            case OR -> executeDistributionForOrNode();
        };
    }

    /**
     * Esegue distribuzione specifica per nodi OR.
     */
    private CNFConverter executeDistributionForOrNode() {
        // Prima distribuisce ricorsivamente su tutti gli operandi
        List<CNFConverter> processedOperands = new ArrayList<>();
        for (CNFConverter operand : operands) {
            processedOperands.add(operand.distributeOrOverAnd());
        }

        // Cerca operando AND per applicare distribuzione
        CNFConverter andOperand = null;
        int andIndex = -1;

        for (int i = 0; i < processedOperands.size(); i++) {
            if (processedOperands.get(i).type == Type.AND) {
                andOperand = processedOperands.get(i);
                andIndex = i;
                break;
            }
        }

        // Se nessun AND trovato, formula già in forma distributiva
        if (andOperand == null) {
            return new CNFConverter(Type.OR, processedOperands);
        }

        // Applica distribuzione: (A | B | (C & D)) -> (A | B | C) & (A | B | D)
        return applyDistributionTransformation(processedOperands, andOperand, andIndex);
    }

    /**
     * Applica la trasformazione distributiva effettiva.
     */
    private CNFConverter applyDistributionTransformation(List<CNFConverter> operands,
                                                         CNFConverter andOperand,
                                                         int andIndex) {
        // Rimuove operando AND dalla lista
        List<CNFConverter> otherTerms = new ArrayList<>(operands);
        otherTerms.remove(andIndex);

        // Distribuisce: per ogni termine di AND, crea nuova clausola OR
        List<CNFConverter> distributedClauses = new ArrayList<>();
        for (CNFConverter andTerm : andOperand.operands) {
            List<CNFConverter> newOrTerms = new ArrayList<>(otherTerms);
            newOrTerms.add(andTerm);

            CNFConverter newOrClause = new CNFConverter(Type.OR, newOrTerms);
            // Distribuzione ricorsiva per AND nidificati
            distributedClauses.add(newOrClause.distributeOrOverAnd());
        }

        return new CNFConverter(Type.AND, distributedClauses);
    }

    //endregion

    //region SEMPLIFICAZIONE STRUTTURALE

    /**
     * Semplifica la struttura della formula eliminando ridondanze e ottimizzando.
     *
     * OTTIMIZZAZIONI APPLICATE:
     * • Appiattimento operatori nidificati: (A & (B & C)) -> (A & B & C)
     * • Eliminazione duplicati: (A | A | B) -> (A | B)
     * • Semplificazione strutturale: singoli operandi estratti
     * • Normalizzazione ordering per confronti
     *
     * @return formula semplificata e ottimizzata
     */
    private CNFConverter simplifyStructure() {
        return switch (this.type) {
            case ATOM -> this; // Caso base: atomi già semplici

            case NOT -> {
                // Verifica e semplifica operando
                if (operand.type == Type.ATOM) {
                    yield this;
                } else {
                    // Semplifica operando e riapplica negazione
                    CNFConverter simplifiedOperand = operand.simplifyStructure();
                    yield new CNFConverter(simplifiedOperand);
                }
            }

            case AND -> simplifyAndNode();
            case OR -> simplifyOrNode();
        };
    }

    /**
     * Semplifica nodo AND con appiattimento e deduplicazione.
     */
    private CNFConverter simplifyAndNode() {
        List<CNFConverter> flattenedOperands = new ArrayList<>();

        for (CNFConverter operand : operands) {
            CNFConverter simplified = operand.simplifyStructure();

            if (simplified.type == Type.AND) {
                // Appiattimento: (A & (B & C)) -> (A & B & C)
                flattenedOperands.addAll(simplified.operands);
            } else {
                flattenedOperands.add(simplified);
            }
        }

        // Eliminazione duplicati preservando ordine
        List<CNFConverter> uniqueOperands = removeDuplicatesPreservingOrder(flattenedOperands);

        return buildOptimalStructure(Type.AND, uniqueOperands);
    }

    /**
     * Semplifica nodo OR con appiattimento e deduplicazione.
     */
    private CNFConverter simplifyOrNode() {
        List<CNFConverter> flattenedOperands = new ArrayList<>();

        for (CNFConverter operand : operands) {
            CNFConverter simplified = operand.simplifyStructure();

            if (simplified.type == Type.OR) {
                // Appiattimento: (A | (B | C)) -> (A | B | C)
                flattenedOperands.addAll(simplified.operands);
            } else {
                flattenedOperands.add(simplified);
            }
        }

        // Eliminazione duplicati preservando ordine
        List<CNFConverter> uniqueOperands = removeDuplicatesPreservingOrder(flattenedOperands);

        return buildOptimalStructure(Type.OR, uniqueOperands);
    }

    /**
     * Rimuove duplicati da lista preservando ordine di apparizione.
     */
    private List<CNFConverter> removeDuplicatesPreservingOrder(List<CNFConverter> operands) {
        List<CNFConverter> unique = new ArrayList<>();
        Set<CNFConverter> seen = new HashSet<>();

        for (CNFConverter operand : operands) {
            if (!seen.contains(operand)) {
                unique.add(operand);
                seen.add(operand);
            }
        }

        return unique;
    }

    /**
     * Costruisce struttura ottimale basata su numero di operandi.
     */
    private CNFConverter buildOptimalStructure(Type type, List<CNFConverter> operands) {
        if (operands.isEmpty()) {
            // Caso degenere: ritorna TRUE per AND vuoto, FALSE per OR vuoto
            return new CNFConverter(type == Type.AND ? "TRUE" : "FALSE");
        } else if (operands.size() == 1) {
            // Ottimizzazione: estrae singolo operando
            return operands.get(0);
        } else {
            // Caso normale: mantiene struttura
            return new CNFConverter(type, operands);
        }
    }

    //endregion

    //region UGUAGLIANZA E HASH

    /**
     * Confronta due formule per uguaglianza strutturale e semantica.
     * Utilizzato per deduplicazione e confronti logici.
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;

        CNFConverter other = (CNFConverter) obj;
        if (this.type != other.type) return false;

        return switch (this.type) {
            case ATOM -> this.atom.equals(other.atom);
            case NOT -> this.operand.equals(other.operand);
            case AND, OR -> {
                if (this.operands.size() != other.operands.size()) {
                    yield false;
                }
                // Confronto set per indipendenza da ordine in AND/OR
                Set<CNFConverter> thisSet = new HashSet<>(this.operands);
                Set<CNFConverter> otherSet = new HashSet<>(other.operands);
                yield thisSet.equals(otherSet);
            }
        };
    }

    /**
     * Calcola hash code consistente con equals per uso in collezioni.
     */
    @Override
    public int hashCode() {
        int result = type.hashCode();

        switch (type) {
            case ATOM -> result = 31 * result + atom.hashCode();
            case NOT -> result = 31 * result + operand.hashCode();
            case AND, OR -> {
                // Hash indipendente da ordine per operatori commutativi
                int operandsHash = 0;
                for (CNFConverter operand : operands) {
                    operandsHash += operand.hashCode(); // Somma commutativa
                }
                result = 31 * result + operandsHash;
            }
        }

        return result;
    }

    //endregion

    //region RAPPRESENTAZIONE TESTUALE

    /**
     * Genera rappresentazione testuale human-readable della formula.
     * Utilizzata per output, debugging e logging.
     *
     * FORMATO OUTPUT:
     * • Atomi: nome variabile (P, Q, R)
     * • Negazioni: !operando (!P, !(P | Q))
     * • Congiunzioni: operando1 & operando2 & ... con parentesi se necessarie
     * • Disgiunzioni: operando1 | operando2 | ... con parentesi se necessarie
     *
     * @return stringa rappresentante la formula in notazione leggibile
     */
    @Override
    public String toString() {
        return switch (this.type) {
            case ATOM -> atom;

            case NOT -> {
                if (operand.type == Type.ATOM) {
                    yield "!" + operand;
                } else {
                    yield "!(" + operand + ")";
                }
            }

            case AND -> {
                if (operands.isEmpty()) yield "";
                if (operands.size() == 1) yield operands.get(0).toString();

                StringBuilder result = new StringBuilder();
                for (int i = 0; i < operands.size(); i++) {
                    if (i > 0) {
                        result.append(" & ");
                    }

                    CNFConverter operand = operands.get(i);
                    if (operand.type == Type.OR) {
                        // Parentesi per precedenza operatori
                        result.append("(").append(operand).append(")");
                    } else {
                        result.append(operand);
                    }
                }
                yield result.toString();
            }

            case OR -> {
                if (operands.isEmpty()) yield "";
                if (operands.size() == 1) yield operands.get(0).toString();

                StringBuilder result = new StringBuilder();
                for (int i = 0; i < operands.size(); i++) {
                    if (i > 0) {
                        result.append(" | ");
                    }
                    result.append(operands.get(i));
                }
                yield result.toString();
            }
        };
    }

    /**
     * Genera rappresentazione compatta per debugging rapido.
     */
    public String toCompactString() {
        return switch (this.type) {
            case ATOM -> atom;
            case NOT -> "!" + operand.toCompactString();
            case AND -> "&(" + operands.size() + ")";
            case OR -> "|(" + operands.size() + ")";
        };
    }

    //endregion

    //region UTILITÀ E ANALISI

    /**
     * Conta il numero di variabili atomiche distinte nella formula.
     */
    public int countUniqueVariables() {
        Set<String> variables = new HashSet<>();
        collectVariables(variables);
        return variables.size();
    }

    /**
     * Raccoglie ricorsivamente tutte le variabili atomiche.
     */
    private void collectVariables(Set<String> variables) {
        switch (this.type) {
            case ATOM -> variables.add(atom);
            case NOT -> operand.collectVariables(variables);
            case AND, OR -> {
                for (CNFConverter operand : operands) {
                    operand.collectVariables(variables);
                }
            }
        }
    }

    /**
     * Calcola la profondità massima dell'albero della formula.
     */
    public int calculateDepth() {
        return switch (this.type) {
            case ATOM -> 0;
            case NOT -> 1 + operand.calculateDepth();
            case AND, OR -> {
                int maxDepth = 0;
                for (CNFConverter operand : operands) {
                    maxDepth = Math.max(maxDepth, operand.calculateDepth());
                }
                yield 1 + maxDepth;
            }
        };
    }

    /**
     * Verifica se un nodo rappresenta una clausola CNF valida.
     */
    private boolean isValidCNFClause() {
        return switch (this.type) {
            case ATOM -> true;
            case NOT -> operand.type == Type.ATOM;
            case OR -> {
                for (CNFConverter operand : operands) {
                    if (operand.type != Type.ATOM &&
                            !(operand.type == Type.NOT && operand.operand.type == Type.ATOM)) {
                        yield false;
                    }
                }
                yield true;
            }
            case AND -> false; // AND non può essere dentro clausole CNF
        };
    }

    //endregion
}