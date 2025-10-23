# Guided Multiplication Factorization (GMF) — README

Dieses Repository enthält ein **Toy‑Modell** für die Idee
> **Faktorisierung als geführte Multiplikation entlang beschränkter Pfade.**

Es ist **rein nummerntheoretisch**, **ohne** Bezüge zu RSA oder anderen Kryptosystemen, und dient dazu,
die Architektur (Promiseklasse, Pfad‑Deskriptoren, Fortschrittsmaß) in kleiner, sicherer Umgebung zu testen.

---

## 1) Idee in 60 Sekunden

Statt „Multiplikation invertieren“ im gesamten Raum, betrachten wir eine **Promiseklasse** \(\mathcal{R}\) von Zahlen \(N\),
für die es **kompakte Pfad‑Deskriptoren** \(\pi\) gibt. Jeder Deskriptor begrenzt, welche lokalen Multiplikations‑Updates \(g_\pi(t)\) erlaubt sind.
Dadurch wird die Suche nach Teilern zu **Pfadsuche** mit **beschränkter Schrittbreite** (bounded width) und **Selbstähnlichkeits‑/Skalenregeln**.

Das Toy‑Skript `gmf_demo.py` zeigt diese Struktur minimalistisch:
- `Mem_R(N)`: Entscheidet die Zugehörigkeit zu einer Spielzeug‑Promiseklasse.
- `Describe(N)`: Liefert wenige Pfad‑Deskriptoren (z. B. „×7“, „×11“ …).
- `GMF_Safe(N)`: Beweisfreundliche Variante mit Log und Fortschrittsprüfung.
- `GMF_Fast(N)`: Heuristische Kurzvariante (klar als heuristisch markiert).

---

## 2) Dateien

- `gmf_demo.py` — lauffähige Demo mit den Funktionen:
  - `Mem_R(N)`, `Describe(N)`, `GMF_Safe(N)`, `GMF_Fast(N)`
  - Hilfsfunktionen: `IsAdmissible`, `LocalStep`, `StepBudget`, `NontrivialGCD`
- (optional) eigene Notebooks/Tests

---

## 3) Installation & Ausführung

Voraussetzungen: Python ≥ 3.8, Standardbibliothek (kein externes Paket nötig).

### a) Direkt ausführen
```bash
python gmf_demo.py
```

**Beispielausgabe:**
```
N=91:    factor=7   log: start: N=91, π[k=7], T=8 / t=0: u=7, g=7, gcd=7 / SUCCESS factor=7
N=77:    factor=7   ...
N=221:   factor=13  ...
N=121:   factor=11  ...
N=997:   factor=1   (N not in toy ℛ)
N=10007: factor=1   (N not in toy ℛ)
```

### b) In eigener Python‑Session verwenden
```python
from gmf_demo import GMF_Safe, GMF_Fast

d, log = GMF_Safe(221)
print(d)      # -> 13 (Nicht‑trivialer Teiler oder 1 falls keiner gefunden)
print(log)    # -> Nachvollziehbares Protokoll der Schritte

print(GMF_Fast(221))  # -> 13 (heuristisch, ohne Log)
```

---

## 4) Interpretation der Ergebnisse

- **Rückgabewert `factor`**:  
  - `> 1`: Nicht‑trivialer Teiler von `N` wurde gefunden.  
  - `== 1`: Kein Faktor gefunden (entweder `N` ist prim/außerhalb der Promiseklasse oder Budget nicht ausreichend).

- **Log (nur Safe‑Mode):**  
  Sequenz der Zustände `u`, verwendetes Update `g` und jeweils `gcd(u, N)`.  
  Sobald ein `gcd` \(>1\) auftritt, ist ein Faktor gefunden (monotone Fortschrittsprüfung).

- **Promiseklasse (Toy):**  
  Im Demo gilt `Mem_R(N) == True`, wenn `N` **mindestens einen kleinen Primfaktor ≤ 97** hat.  
  Diese Wahl ist **nur** für die Demonstration — du kannst/ sollst `Mem_R` und `Describe` später durch deine echte Klassendefinition ersetzen.

---

## 5) Architektur‑Hooks (wo du ansetzt)

- `Mem_R(N)`: **entscheidbarer** Test, ob `N ∈ ℛ`.  
- `Describe(N)`: gibt eine **kleine** Menge an Pfad‑Deskriptoren zurück (z. B. Residuen‑/Blockregeln, Skalen‑Constraints).  
- `LocalStep(π, state)`: erzeugt ein zulässiges lokales Update `g`.  
- `IsAdmissible(π, g, t)`: prüft, ob `g` zur **beschränkten Schrittbreite** & **Skalenregel** passt.  
- `Delta(u, N)` (optional): deterministisches Fortschrittsmaß (im Demo nicht strikt notwendig, aber hilfreich für Beweise).  
- `StepBudget(π, N)`: setzt die Obergrenze der Schrittzahl (z. B. polylog in `N`).

Diese Hooks erlauben dir, die **fraktalen/selbstähnlichen Pfade** deiner Theorie einzubauen, **ohne** die Struktur zu verändern.

---

## 6) Grenzen des Toy‑Modells

- Die Promiseklasse ist absichtlich banal gewählt (kleiner Primfaktor ≤ 97), um **keine** realen Instanzprofile abzubilden.  
- Das Demo ist **kein** Faktorisierungsangriff, sondern ein **Struktur‑Proof‑of‑Concept**.  
- Performanceaussagen sind **nicht** auf reale, große Instanzen übertragbar.

---

## 7) Sicherheit & Governance

- Kein Instanzgenerator, **keine** Hinweise auf Produktivschlüssel, **kein** Kryptobezug.  
- Logs sind nachvollziehbar, aber enthalten **keine sensiblen Daten**.  
- Wenn du eigene Deskriptoren einbaust: **keine** realweltlichen Parameter/Seeds veröffentlichen; intern testen.

---

## 8) Nächste Schritte (optional)

- **Unit‑Tests** (pytest) für `GMF_Safe`/`Mem_R`/`Describe`.  
- **Delta‑Definition** konkretisieren (monotone Invariante).  
- **Formale Spezifikation** der Deskriptoren (z. B. als kleine DSL oder JSON‑Schema).  
- **LaTeX‑Integration:** Abschnitt aus `section_guided_multiplication.tex` (separat verfügbar) in Paper einbinden.

---

## 9) FAQ (kurz)

**Q:** Warum gibt `GMF_Safe` manchmal `1` zurück?  
**A:** Dann liegt `N` im Toy ggf. **nicht** in \(\mathcal{R}\) (z. B. prim oder alle Primfaktoren > 97) oder das Schrittbudget reichte nicht.

**Q:** Wo passe ich die Pfadlogik an?  
**A:** In `Describe`, `LocalStep`, `IsAdmissible` und (falls genutzt) `Delta`/`StepBudget`.

**Q:** Ist das ein Kryptotool?  
**A:** Nein. Reine Demo der **Strukturidee** „geführte Multiplikation“ auf einer harmlosen Promiseklasse.
