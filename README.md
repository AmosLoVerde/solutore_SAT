# Solutore SAT CDCL - README

## Introduzione

Questo software implementa un **solutore SAT** basato sull'algoritmo **CDCL** (_Conflict-Driven Clause Learning_) per la risoluzione di problemi di soddisfacibilità booleana. Il solutore include tecniche avanzate state-of-the-art per l'ottimizzazione delle performance e la generazione di prove matematiche.

### Tecniche Implementate

**Algoritmo CDCL Core:**
- **Euristica 1UIP** (First Unique Implication Point) per l'apprendimento di clausole
- **Euristica VSIDS** (Variable State Independent Decaying Sum) per la selezione delle variabili

**Opzioni aggiuntive:**
- **Tecnica del reinizio** - Reinizio periodico ogni 5 conflitti con sussunzione automatica
- **Principio di sussunzione** - Eliminazione clausole sovrainsieme di altre clausole
- **Trasformazione Tseitin** - Conversione in E-CNF equisoddisfacibile

**Funzionalità Aggiuntive:**
- **Generatore Pigeonhole Problem** - Creazione automatica di istanze di test UNSAT
- **Conversione CNF Standard** - Supporto per file in formato DIMACS
- **Parser ANTLR** - Supporto per formule in notazione matematica standard

---

## Installazione e Configurazione

### Prerequisiti di Sistema

Il software richiede:
- **Java SDK 20** o superiore
- **Gradle** (incluso nel progetto tramite Gradle Wrapper)
- Sistema operativo: Linux, Windows, o macOS

### 1. Download del solutore

#### Clona il Repository
```bash
git clone https://github.com/AmosLoVerde/solutore_SAT.git
cd solutore_SAT
```

#### Oppure Estrai l'Archivio
```bash
# Linux/macOS
unzip solutore_SAT.tgz
cd solutore_SAT

# Windows
# Estrai l'archivio ZIP usando WinRAR/7-Zip
# Apri il Prompt dei comandi nella directory estratta
```

### 2. Compilazione del Progetto

Il progetto utilizza **Gradle Wrapper**, quindi non è necessario installare Gradle separatamente.

#### Linux/macOS
```bash
# Rendi eseguibile il wrapper (solo la prima volta)
chmod +x gradlew

# Compila il progetto
./gradlew build

# Crea il JAR eseguibile
./gradlew jar
```

#### Windows
```cmd
# Compila il progetto
gradlew.bat build

# Crea il JAR eseguibile
gradlew.bat jar
```

### 3. Verifica installazione

Dopo la compilazione, effettua una verifica che tutto funzioni correttamente:

```bash
# Linux/macOS
java -jar build/libs/build/libs/solutore_SAT.jar -h

# Windows
java -jar build\libs\solutore_SAT.jar -h
```

Dovresti vedere l'help del programma. Se appare un errore, verifica:
1. Che Java SDK 20 sia installato correttamente
2. Che la compilazione sia avvenuta senza errori
3. Che il file JAR esista nella directory `build/libs/`

---

## Utilizzo del software

### Sintassi generale

```bash
java -jar build/libs/solutore_SAT.jar [opzioni]
```

### Parametri disponibili

| Parametro | Descrizione | Esempio |
|-----------|-------------|---------|
| `-f <file>` | Elabora un singolo file .txt o .cnf | `-f formula.txt` |
| `-d <directory>` | Elabora tutti i file in una directory | `-d ./problemi/` |
| `-o <directory>` | Directory di output personalizzata | `-o ./risultati/` |
| `-t <secondi>` | Timeout per singola formula (min: 5s) | `-t 30` |
| `-opt=<flags>` | Opzioni aggiuntive (s,t,r,all) | `-opt=sr` |
| `-convert` | Modalità conversione diretta CNF | `-convert` |
| `-gen=<tipo> <numero>` | Genera istanze di test del problema Pigeonhole | `-gen=pigeonhole 10` |
| `-h` | Mostra help completo | `-h` |

### Opzioni aggiuntive (-opt)

| Flag | Tecnica | Descrizione |
|------|---------|-------------|
| `s` | Sussunzione | Elimina clausole che sono sovrainsieme |
| `t` | Tseitin | Conversione E-CNF equisoddisfacibile |
| `r` | Restart | Reinizio periodico ogni 5 conflitti con sussunzione |
| `all` | Tutte | Attiva tutte le opzioni aggiuntive |

---

## Esempi di utilizzo dettagliati

### 1. Risoluzione SAT - file singolo base

```bash
java -jar build/libs/solutore_SAT.jar -f formula.txt
```

**Input (formula.txt):**
```
(P | Q) & (!P | R) & (!Q | !R)
```

**Output prodotto:**
```
Directory corrente/
├── CNF/
│   └── formula.cnf          # Formula convertita in CNF
├── RESULT/
│   └── formula.result       # Risultato
└── STATS/
    └── opzioni_attive.txt   # Opzioni utilizzate (nessuna)
```

### 2. Risoluzione SAT - con tutte le ottimizzazioni

```bash
java -jar build/libs/solutore_SAT.jar -f complex_formula.txt -opt=all -t 60
```

**Output Prodotto:**
```
Directory corrente/
├── CNF/
│   └── complex_formula.cnf
├── E-CNF/
│   └── complex_formula.ecnf     # Formula Tseitin
├── RESULT/
│   └── complex_formula.result
└── STATS/
    ├── opzioni_attive.txt
    ├── TSEITIN/
    │   └── complex_formula.stats
    ├── SUBSUMPTION/
    │   └── complex_formula.stats
    └── RESTART/
        └── complex_formula.stats
```

### 3. Elaborazione di una directory

```bash
java -jar build/libs/solutore_SAT.jar -d ./test_problems/ -opt=sr -o ./results/
```

**Struttura input:**
```
test_problems/
├── sat_example1.txt
├── sat_example2.txt
└── unsat_example.txt
```

### 4. Utilizzo diretto dello standard DIMACS

```bash
java -jar build/libs/solutore_SAT.jar -f problem.cnf -convert -opt=s
```

**Output prodotto:**
```
results/
├── RESULT/
│   └── problem.result       # Risultato diretto (nessun file CNF/ generato)
└── STATS/
    ├── opzioni_attive.txt
    └── SUBSUMPTION/
        └── problem.stats
```

### 5. Generazione delle istanze di Pigeonhole problem

```bash
java -jar build/libs/solutore_SAT.jar -gen=pigeonhole 5 -o ./pigeonhole_tests/
```

**Struttura output:**
```
pigeonhole_tests/
└── PIGEONHOLE/
    ├── pigeonhole_1.txt     # 1 buca, 2 piccioni
    ├── pigeonhole_2.txt     # 2 buche, 3 piccioni  
    ├── pigeonhole_3.txt     # 3 buche, 4 piccioni
    ├── pigeonhole_4.txt     # 4 buche, 5 piccioni
    └── pigeonhole_5.txt     # 5 buche, 6 piccioni
```

### 6. Elaborazione con Timeout personalizzato

```bash
java -jar build/libs/solutore_SAT.jar -f difficult_problem.txt -t 120
```

---

## Note Operative

### Formati di Input Supportati

#### File .txt - Formule logiche in notazione matematica

Il software supporta formule logiche proposizionali arbitrarie scritte usando la seguente sintassi:

**Operatori Logici:**
| Operatore | Simboli Supportati | Esempio |
|-----------|-------------------|---------|
| **NOT** (Negazione) | `!`, `'not'`, `'NOT'` | `!P`, `not Q`, `NOT R` |
| **AND** (Congiunzione) | `&`, `'and'`, `'AND'` | `P & Q`, `P and Q`, `P AND Q` |
| **OR** (Disgiunzione) | `\|`, `'or'`, `'OR'` | `P \| Q`, `P or Q`, `P OR Q` |
| **IMPLIES** (Implicazione) | `->`, `'=>'`, `'implies'`, `'IMPLIES'` | `P -> Q`, `P => Q`, `P implies Q` |
| **IFF** (Biimplicazione) | `<->`, `'<=>'`, `'iff'`, `'IFF'` | `P <-> Q`, `P <=> Q`, `P iff Q` |

**Simboli Speciali:**
| Simbolo | Descrizione | Esempio |
|---------|-------------|---------|
| `(` `)` | Parentesi per precedenza | `(P & Q) | R` |
| `'top'`, `'TOP'` | Costante logica TRUE | `P & TOP` |
| `'bottom'`, `'BOTTOM'` | Costante logica FALSE | `P | BOTTOM` |

**Identificatori di Variabili:**
- Alfanumerici che iniziano con lettera: `P`, `Q`, `var1`, `myVariable`
- Case-sensitive: `P` e `p` sono variabili diverse

**Esempi di Formule Valide:**
```
# Formula semplice
P & Q

# Formula con implicazione
(P & Q) -> R

# Formula complessa con biimplicazione
((P | Q) & !R) <-> (S implies T)

# Uso di costanti
P & TOP | (Q -> BOTTOM)

# Sintassi alternativa con parole chiave
P and Q or not R implies S iff T

# Formula con parentesi per precedenza
!(P & Q) | (R <-> S)
```

#### File .cnf - Formato DIMACS standard
```
c commento
p cnf 3 2
1 -2 3 0
-1 2 0
4 -9 11 0
-2 -3 0
```

### Organizzazione dell'utput

Il software crea automaticamente una struttura organizzata:

```
Output Directory/
├── CNF/              # Formule convertite (non in modalità -convert)
├── E-CNF/            # Trasformazioni Tseitin (se -opt=t, -opt=ts, -opt=tr, -opt=all)  
├── RESULT/           # Risultati finali con modelli/prove
├── STATS/            # Statistiche dettagliate
│   ├── TSEITIN/      # Metriche conversione Tseitin
│   ├── SUBSUMPTION/  # Metriche eliminazione clausole
│   └── RESTART/      # Metriche reinizio
└── PIGEONHOLE/       # Istanze generate (se -gen=pigeonhole)
```

---
