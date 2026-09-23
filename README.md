# CNF Learning Studio — fixed version

## Features
- Proper CNF explanation
- Formal CNF rule checklist
- Six-stage conversion timeline
- Epsilon/nullable handling
- Unit-production removal
- Useless-symbol removal (generating + reachable)
- Terminal isolation
- Binarization
- Final CNF structural verification
- Before/after display for every stage
- Parse-tree visualizer
- Practice mode with instant feedback and score
- CNF validator
- Responsive cinematic dark UI

## Windows / PowerShell

Open this folder in VS Code. In the terminal, make sure `package.json` is visible:

```powershell
dir package.json
```

Then:

```powershell
npm.cmd install
npm.cmd run dev
```

If `dir package.json` says it cannot find the file, you are in the wrong folder. `cd` into the folder that contains `package.json`.

Example:

```powershell
cd C:\Bablu\cnf-learning-studio
npm.cmd install
npm.cmd run dev
```

## Grammar format

Use:

```text
S -> AB | a
A -> a | ε
B -> b
```

For clarity, multi-character non-terminals can be written with spaces:

```text
S -> A B
A -> a
B -> b
```
