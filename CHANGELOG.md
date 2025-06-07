# Changelog

Tutte le modifiche significative a questo progetto sono documentate in questo file.

Il formato segue le linee guida di [Keep a Changelog](https://keepachangelog.com/it-IT/1.0.0/)
e adotta il [versionamento semantico](https://semver.org/lang/it/).

## [1.7.1] - 2025-06-07
### Fixed
- Migliorata la struttura e l’organizzazione dei file `.stats` nella cartella `STATS`.
- Aggiunto il file `opzioni_attive.txt` per indicare le opzioni attive durante
  l’esecuzione del solutore.


## [1.7.0] - 2025-06-07
### Added
- Implementato il principio di sussunzione nel file `SubsumptionPrinciple.java`,
  per eliminare clausole che sono sovrainsieme di altre. È applicabile sia alle formule CNF sia alle formule E-CNF, quest'ultime ricavate tramite la trasformazione di Tseitin.

### Changed
- Rinominato il package `optimization` in `optionalfeatures`, perché il nome è più affine a ciò che necessita il progetto.


## [1.6.1] - 2025-06-07
### Fixed
- Migliorato il contenuto dei file `.result` generati dal risolutore:
  ora riportano il tipo di formula (CNF oppure E-CNF), il numero di propagazioni
  e il numero di clausole apprese.


## [1.6.0] - 2025-06-07
### Added
- Implementata la trasformazione in forma normale congiunta equisoddisfacibile (E-CNF)
  mediante la procedura di **Tseitin**, per una rappresentazione più compatta ed efficiente
  delle formule logiche in CNF. In particolare è stata creato il package `optimization` con all'interno `TseitinConverter.java`


## [1.5.3] - 2025-06-06
### Fixed
- Ultimata la generazione della prova nel modulo CDCL. La procedura
  è ora considerata stabile e corretta, salvo imprevisti non noti.


## [1.5.2] - 2025-06-05
### Fixed
- Ulteriore miglioramento della generazione della prova all’interno del solver CDCL.
  La logica di costruzione è ora più coerente e robusta, anche se potrà ancora essere
  raffinata in release successive.


## [1.5.1] - 2025-06-02
### Fixed
- Migliorata la generazione della prova nel modulo CDCL:
  ora la costruzione delle clausole apprese è più accurata e coerente.
  Ulteriori raffinamenti sono ancora possibili.


## [1.5.0] - 2025-06-01
### Added
- Prima versione dell'algoritmo CDCL con supporto per:
  - Euristica 1UIP (First Unique Implication Point) per l'apprendimento dei conflitti
  - Euristica VSIDS per la scelta delle variabili decisionali
  - Generazione della prova (in fase di sviluppo)

- Creato il package `cdcl` con i seguenti file:
  - `CDCLSolver.java`
  - `CDCLSupport.java`
  - `ProofGenerator.java`
  - `SATResult.java`
  - `SATStatistics.java`

⚠️ Nota: la generazione della prova non è ancora completamente funzionante
e la procedura necessita di ulteriore validazione e revisione dei commenti.


## [1.4.0] - 2025-05-22
### Changed
- Separata la logica di parsing e conversione in CNF:
  - Creato il file `LogicFormulaParser.java` per contenere tutti i metodi `visit`
    responsabili della visita dell'albero sintattico generato da ANTLR.
  - `CNFConverter.java` ora contiene unicamente i metodi per convertire una formula
    logica in forma normale congiuntiva (CNF).
- Rimossa la classe interna `Formula`, ora completamente rifattorizzata.


## [1.3.0] - 2025-05-02
### Added
- Aggiunta l'opzione `-o <percorso>` alla riga di comando per permettere
  all’utente di specificare la directory di destinazione dei file di output.

## [1.2.1] - 2025-05-01
### Fixed
- Modificata la classe `CNFConverter` per evitare la semplificazione automatica
  di sottoformule sempre vere. Ora tali parti vengono mantenute in forma esplicita
  nella traduzione in CNF, per migliorare la chiarezza del risultato.

## [1.2.0] - 2025-05-01
### Added
- Aggiunta l'opzione `-d <percorso_cartella>` alla CLI per eseguire il processo
  su tutti i file `.txt` presenti nella cartella specificata.
- Validazione degli argomenti: le opzioni `-f` e `-d` sono ora mutuamente esclusive.

## [1.1.1] - 2025-05-01
### Fixed
- Corretto un bug nella classe `CNFConverter` che causava una conversione errata di alcune formule logiche complesse in forma normale congiuntiva (CNF).

## [1.1.0] - 2025-05-01
### Added
- Aggiunta la classe `CNFConverter` per convertire formule in logica proposizionale in CNF.
- Creato il package `cnf` per organizzare la logica di conversione.
- Aggiunti i metodi `readFileContent` e `saveCNFFormula` nella classe `Main` per la gestione dell'I/O su file.
- Modificato `processFile` per elaborare e convertire la formula logica da file in CNF e salvare il risultato su un nuovo file `.cnf`.

## [1.0.1] - 2025-05-01
### Fixed
- Migliorata la grammatica `LogicFormula.g4` per gestire correttamente la precedenza tra i connettivi logici (¬, ∧, ∨, →, ↔) durante il parsing.

## [1.0.0] - 2025-04-30
### Added
- Inizializzato il progetto SAT con Gradle.
- Aggiunto supporto per l'esecuzione via terminale con le opzioni `-f` (file di input) e `-h` (help).
- Creato il package `antlr.org.sat.parser` con la grammatica `LogicFormula.g4` per il parsing di formule logiche in input.
