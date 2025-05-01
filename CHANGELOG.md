# Changelog

Tutte le modifiche significative a questo progetto sono documentate in questo file.

Il formato segue le linee guida di [Keep a Changelog](https://keepachangelog.com/it-IT/1.0.0/)
e adotta il [versionamento semantico](https://semver.org/lang/it/).

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
