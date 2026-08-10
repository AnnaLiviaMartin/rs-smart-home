# Formale Spezifikation und Verifikation eines Zutritts- und Bewegungssystems mit Alloy und Lean

Dieses Projekt untersucht die formale Modellierung und Verifikation eines Smart-Home-Systems mit Fokus auf Anwesenheitserkennung und Zutrittskontrolle

Zur Modellierung und Analyse werden **Alloy 6** und **Lean 4** verwendet.

## Motivation, Fachliche Systembeschreibung, Modellherleitung

Die Herleitung des Smart-Home-Modells befindet sich in [Idee.md](IDEE.md)

## Modellbeschreibung

Die fachliche Beschreibung der Bedingungen der einzelnen Event-B-Schritte des Smart-Home-Modells befindet sich in [Model_Spezifikation.md](MODEL_SPEZIFIKATION.md.md)

## Beschreibung relevanter Umsetzungsentscheidungen

Die Beschreibung der Umsetzung der einzelnen Event-B-Schritte des Smart-Home-Modells befindet sich in [Umsetzung.md](UMSETZUNG.md)

## Code

### Projektstruktur


```text
project/
│
├── README.md
├── MODEL_SPECIFICATION.md
│
├── alloy/
│   ├── smart_home.als
│
├── lean/
│   ├── SmartHome.lean
│
└── docs/
    └── diagrams/
```

In den Unterordnern alloy und lean sind die jeweiligen Umsetzungen der Idee zu finden. Unter docs können alle Diagramme und Bilder gefunden werden.

### Alloy ausführen

Modell laden:

```text
alloy/smart_home.als
```

Analyse starten:

```alloy
run {}
```

oder

```alloy
check PropertyName
```

Die Style-Datei für's Ansehen des Alloy-Modells, findet sich unter ./alloy/todo.td

### Lean ausführen

Projekt bauen:

```bash
lake build
```

Einzelne Datei prüfen:

```bash
lean SmartHome.lean
```

Lean ist in zwei Dateien aufgesplittet. Die erste Datei todo.td stellt die Beweise bereit. Die zweite Datei todo2.td stellt ein Beispiel zur Verfügung.