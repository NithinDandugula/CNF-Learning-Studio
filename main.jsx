import React, { useMemo, useState } from "react";
import { createRoot } from "react-dom/client";
import {
  BookOpen, CheckCircle2, ChevronLeft, ChevronRight, Code2, GitBranch,
  GraduationCap, Lightbulb, Play, RotateCcw, ShieldCheck, Sparkles,
  Target, Terminal, XCircle, Zap
} from "lucide-react";
import "./styles.css";

/* =========================================================
   CNF ENGINE
   Correct teaching-oriented pipeline:
   1. Add new start symbol
   2. Remove epsilon productions
   3. Remove unit productions
   4. Remove useless symbols
      a) non-generating
      b) unreachable
   5. Replace terminals in RHS length >= 2
   6. Binarize RHS length > 2
   Final invariant:
      A -> BC
      A -> a
      S -> ε (only when ε is in the language)
   ========================================================= */

const EXAMPLES = {
  basic: {
    name: "Basic",
    grammar: "S -> AB | a\nA -> a\nB -> b",
    note: "Already close to CNF."
  },
  full: {
    name: "Full Conversion",
    grammar: "S -> AB | aA\nA -> aA | ε\nB -> bB | b",
    note: "Exercises ε-removal and terminal isolation."
  },
  unit: {
    name: "Unit + Useless",
    grammar: "S -> A | a\nA -> B | a\nB -> b\nC -> d\nD -> E\nE -> F",
    note: "Exercises unit removal and useless-symbol removal."
  },
  long: {
    name: "Long Rules",
    grammar: "S -> ABCD | aBC\nA -> a\nB -> b\nC -> c\nD -> d",
    note: "Exercises terminal isolation and binarization."
  },
  nullable: {
    name: "Nullable",
    grammar: "S -> AB | b\nA -> a | ε\nB -> c | ε",
    note: "Shows all valid nullable combinations."
  }
};

function cleanLine(line) {
  return line.replace(/→/g, "->").replace(/=>/g, "->").trim();
}

function tokenizeRhs(rhs) {
  const s = rhs.replace(/\s+/g, "");
  if (!s || s === "ε" || s.toLowerCase() === "epsilon") return [];
  // Supports X Y Z notation and compact conventional grammar notation.
  if (/\s/.test(rhs.trim())) return rhs.trim().split(/\s+/);
  return [...s];
}

function parseGrammar(text) {
  const rules = [];
  let start = null;
  const errors = [];
  for (const raw of text.split(/\r?\n/)) {
    const line = cleanLine(raw);
    if (!line || line.startsWith("#")) continue;
    const parts = line.split("->");
    if (parts.length !== 2) {
      errors.push(`Invalid rule: "${raw}"`);
      continue;
    }
    const lhs = parts[0].trim();
    if (!/^[A-Za-z][A-Za-z0-9_]*$/.test(lhs)) {
      errors.push(`Invalid non-terminal: "${lhs}"`);
      continue;
    }
    if (!start) start = lhs;
    const alternatives = parts[1].split("|");
    for (const alt of alternatives) {
      const rhs = alt.trim();
      const symbols = tokenizeRhs(rhs);
      rules.push({ lhs, rhs: symbols });
    }
  }
  const nts = new Set(rules.map(r => r.lhs));
  return { rules, start, nts, errors };
}

function keyRule(r) { return `${r.lhs}->${r.rhs.join(" ") || "ε"}`; }

function dedupeRules(rules) {
  const seen = new Set();
  return rules.filter(r => {
    const k = keyRule(r);
    if (seen.has(k)) return false;
    seen.add(k);
    return true;
  });
}

function formatRules(rules) {
  const grouped = new Map();
  for (const r of rules) {
    if (!grouped.has(r.lhs)) grouped.set(r.lhs, []);
    grouped.get(r.lhs).push(r.rhs.length ? r.rhs.join(" ") : "ε");
  }
  return [...grouped.entries()]
    .map(([lhs, rhss]) => `${lhs} → ${[...new Set(rhss)].join(" | ")}`)
    .join("\n");
}

function cloneRules(rules) {
  return rules.map(r => ({ lhs: r.lhs, rhs: [...r.rhs] }));
}

function freshName(base, used, prefix = "X") {
  let i = 0;
  let candidate = base;
  while (used.has(candidate)) candidate = `${prefix}${++i}`;
  used.add(candidate);
  return candidate;
}

function nullableSet(rules) {
  const n = new Set();
  let changed = true;
  while (changed) {
    changed = false;
    for (const r of rules) {
      if (r.rhs.length === 0 || r.rhs.every(s => n.has(s))) {
        if (!n.has(r.lhs)) { n.add(r.lhs); changed = true; }
      }
    }
  }
  return n;
}

function removeEpsilon(rules, start, allowStartEpsilon) {
  const nullable = nullableSet(rules);
  const out = [];
  for (const r of rules) {
    if (r.rhs.length === 0) continue;
    const positions = [];
    r.rhs.forEach((s, i) => { if (nullable.has(s)) positions.push(i); });
    const combinations = 1 << Math.min(positions.length, 20);
    for (let mask = 0; mask < combinations; mask++) {
      const remove = new Set();
      positions.forEach((pos, j) => { if (mask & (1 << j)) remove.add(pos); });
      const rhs = r.rhs.filter((_, i) => !remove.has(i));
      if (rhs.length || (allowStartEpsilon && r.lhs === start)) out.push({ lhs: r.lhs, rhs });
    }
  }
  return dedupeRules(out);
}

function removeUnits(rules) {
  const nts = new Set(rules.map(r => r.lhs));
  const byLhs = new Map();
  for (const nt of nts) byLhs.set(nt, []);
  for (const r of rules) byLhs.get(r.lhs)?.push(r);

  const out = [];
  for (const A of nts) {
    const closure = new Set([A]);
    const queue = [A];
    while (queue.length) {
      const x = queue.shift();
      for (const r of byLhs.get(x) || []) {
        if (r.rhs.length === 1 && nts.has(r.rhs[0]) && !closure.has(r.rhs[0])) {
          closure.add(r.rhs[0]); queue.push(r.rhs[0]);
        }
      }
    }
    for (const x of closure) {
      for (const r of byLhs.get(x) || []) {
        if (!(r.rhs.length === 1 && nts.has(r.rhs[0]))) out.push({ lhs: A, rhs: [...r.rhs] });
      }
    }
  }
  return dedupeRules(out);
}

function removeUseless(rules, start) {
  const nts = new Set(rules.map(r => r.lhs));
  const generating = new Set();

  let changed = true;
  while (changed) {
    changed = false;
    for (const r of rules) {
      const good = r.rhs.length === 0 || r.rhs.every(s => !nts.has(s) || generating.has(s));
      if (good && !generating.has(r.lhs)) { generating.add(r.lhs); changed = true; }
    }
  }

  let filtered = rules.filter(r =>
    generating.has(r.lhs) && r.rhs.every(s => !nts.has(s) || generating.has(s))
  );

  const reachable = new Set([start]);
  changed = true;
  while (changed) {
    changed = false;
    for (const r of filtered) {
      if (!reachable.has(r.lhs)) continue;
      for (const s of r.rhs) {
        if (new Set(filtered.map(x => x.lhs)).has(s) && !reachable.has(s)) {
          reachable.add(s); changed = true;
        }
      }
    }
  }
  filtered = filtered.filter(r => reachable.has(r.lhs));
  return dedupeRules(filtered);
}

function isolateTerminals(rules) {
  const used = new Set(rules.map(r => r.lhs));
  const terminalVars = new Map();
  const added = [];
  const out = [];

  for (const r of rules) {
    if (r.rhs.length < 2) { out.push({ lhs: r.lhs, rhs: [...r.rhs] }); continue; }
    const rhs = r.rhs.map(s => {
      if (/^[a-z0-9]$/.test(s)) {
        if (!terminalVars.has(s)) {
          const v = freshName("T", used, "T");
          terminalVars.set(s, v);
          added.push({ lhs: v, rhs: [s] });
        }
        return terminalVars.get(s);
      }
      return s;
    });
    out.push({ lhs: r.lhs, rhs });
  }
  return dedupeRules([...out, ...added]);
}

function binarize(rules) {
  const used = new Set(rules.map(r => r.lhs));
  const out = [];
  let counter = 0;
  for (const r of rules) {
    if (r.rhs.length <= 2) { out.push({ lhs: r.lhs, rhs: [...r.rhs] }); continue; }
    let left = r.lhs;
    let rest = [...r.rhs];
    while (rest.length > 2) {
      const v = freshName(`X${++counter}`, used, "X");
      out.push({ lhs: left, rhs: [rest[0], v] });
      left = v;
      rest = rest.slice(1);
    }
    out.push({ lhs: left, rhs: rest });
  }
  return dedupeRules(out);
}

function isCNF(rules, start) {
  for (const r of rules) {
    if (r.rhs.length === 0) {
      if (r.lhs !== start) return false;
    } else if (r.rhs.length === 1) {
      if (!/^[a-z0-9]$/.test(r.rhs[0])) return false;
    } else if (r.rhs.length === 2) {
      if (!r.rhs.every(s => /^[A-Z][A-Za-z0-9_]*$/.test(s))) return false;
    } else return false;
  }
  return true;
}

function convertCNF(input) {
  const parsed = parseGrammar(input);
  if (parsed.errors.length || !parsed.rules.length) {
    return { ok: false, errors: parsed.errors.length ? parsed.errors : ["No grammar rules found."] };
  }
  let rules = cloneRules(parsed.rules);
  let start = parsed.start;
  const steps = [];
  const originalHasEpsilon = rules.some(r => r.lhs === start && r.rhs.length === 0);

  const addStep = (title, subtitle, why, before, after, focus) => {
    steps.push({ title, subtitle, why, before, after, focus });
  };

  if (rules.some(r => r.rhs.includes(start))) {
    const used = new Set(rules.map(r => r.lhs));
    const ns = freshName("S0", used, "S");
    const before = cloneRules(rules);
    rules = dedupeRules([{ lhs: ns, rhs: [start] }, ...rules]);
    start = ns;
    addStep("Add a new start symbol", "Step 1", "The start symbol must not appear on a right-hand side when we need to preserve ε cleanly.", before, rules, "new-start");
  } else {
    addStep("Start symbol check", "Step 1", "A fresh start symbol is only needed when the original start occurs on a right-hand side.", rules, rules, "new-start");
  }

  {
    const before = cloneRules(rules);
    const allow = originalHasEpsilon || nullableSet(rules).has(start);
    rules = removeEpsilon(rules, start, allow);
    if (allow && !rules.some(r => r.lhs === start && r.rhs.length === 0)) rules.push({ lhs: start, rhs: [] });
    rules = dedupeRules(rules);
    addStep("Remove ε-productions", "Step 2", "Find nullable variables, then add every valid combination obtained by optionally deleting nullable symbols. Keep S → ε only when ε belongs to the language.", before, rules, "epsilon");
  }

  {
    const before = cloneRules(rules);
    rules = removeUnits(rules);
    addStep("Remove unit productions", "Step 3", "A unit production has the form A → B. Replace it by the non-unit productions reachable through the unit chain.", before, rules, "unit");
  }

  {
    const before = cloneRules(rules);
    rules = removeUseless(rules, start);
    addStep("Remove useless symbols", "Step 4", "First remove non-generating symbols, then remove symbols that cannot be reached from the start symbol.", before, rules, "useless");
  }

  {
    const before = cloneRules(rules);
    rules = isolateTerminals(rules);
    addStep("Replace terminals in long rules", "Step 5", "CNF allows A → a, but a terminal cannot appear beside other symbols. Give each terminal a helper variable.", before, rules, "terminals");
  }

  {
    const before = cloneRules(rules);
    rules = binarize(rules);
    addStep("Binarize long productions", "Step 6", "CNF allows at most two symbols on the right. Split every RHS of length 3 or more into binary rules using fresh helper variables.", before, rules, "binary");
  }

  const final = dedupeRules(rules);
  return {
    ok: isCNF(final, start),
    start,
    original: parsed,
    steps,
    final,
    errors: isCNF(final, start) ? [] : ["The internal conversion did not reach CNF."]
  };
}

/* ---------------- Parse tree / derivation ---------------- */

function buildParseTree(grammarText, input) {
  const g = parseGrammar(grammarText);
  if (!g.start) return { ok: false, message: "Enter a grammar first." };
  const target = [...input.replace(/\s+/g, "")];
  const rulesBy = new Map();
  for (const r of g.rules) {
    if (!rulesBy.has(r.lhs)) rulesBy.set(r.lhs, []);
    rulesBy.get(r.lhs).push(r.rhs);
  }

  const memo = new Map();
  const visiting = new Set();

  function derive(sym, i, j, depth=0) {
    const key = `${sym}|${i}|${j}`;
    if (memo.has(key)) return memo.get(key);
    if (depth > 30 || visiting.has(key)) return null;
    visiting.add(key);

    for (const rhs of rulesBy.get(sym) || []) {
      if (rhs.length === 0) {
        if (i === j) {
          const node = { sym, children: [] };
          memo.set(key, node); visiting.delete(key); return node;
        }
        continue;
      }
      if (rhs.length === 1 && !rulesBy.has(rhs[0])) {
        if (j === i + 1 && target[i] === rhs[0]) {
          const node = { sym, children: [{ sym: rhs[0], terminal: true }] };
          memo.set(key, node); visiting.delete(key); return node;
        }
        continue;
      }
      // General CFG rule using split-point search.
      const parts = rhs;
      function matchPart(k, pos) {
        if (k === parts.length) return pos === j ? [] : null;
        const childSym = parts[k];
        const isTerminal = !rulesBy.has(childSym);
        if (isTerminal) {
          if (pos < j && target[pos] === childSym) {
            const rest = matchPart(k + 1, pos + 1);
            if (rest) return [{ sym: childSym, terminal: true }, ...rest];
          }
          return null;
        }
        for (let end = pos; end <= j; end++) {
          const child = derive(childSym, pos, end, depth + 1);
          if (!child) continue;
          const rest = matchPart(k + 1, end);
          if (rest) return [child, ...rest];
        }
        return null;
      }
      const children = matchPart(0, i);
      if (children) {
        const node = { sym, children };
        memo.set(key, node); visiting.delete(key); return node;
      }
    }
    visiting.delete(key);
    memo.set(key, null);
    return null;
  }

  const tree = derive(g.start, 0, target.length);
  if (!tree) return { ok: false, message: `No derivation found for "${input}". Try a string generated by the grammar.` };
  return { ok: true, tree, start: g.start, input: target.join(" ") };
}

function TreeNode({ node, level=0 }) {
  return (
    <div className="tree-node" style={{"--level": level}}>
      <div className={`node-pill ${node.terminal ? "terminal" : ""}`}>{node.sym}</div>
      {node.children?.length > 0 && (
        <div className="tree-children">
          {node.children.map((c,i)=><TreeNode node={c} level={level+1} key={i}/>)}
        </div>
      )}
    </div>
  );
}

/* ---------------- UI ---------------- */

const NAV = [
  ["learn","Learn",BookOpen],
  ["convert","Converter",Zap],
  ["tree","Parse Tree",GitBranch],
  ["practice","Practice",Target],
  ["validate","Validator",ShieldCheck]
];

function App() {
  const [intro, setIntro] = useState(true);
  const [tab, setTab] = useState("learn");
  const [grammar, setGrammar] = useState(EXAMPLES.full.grammar);
  const [conversion, setConversion] = useState(() => convertCNF(EXAMPLES.full.grammar));
  const [step, setStep] = useState(0);
  const [treeGrammar, setTreeGrammar] = useState("S -> AB\nA -> a\nB -> b");
  const [treeInput, setTreeInput] = useState("ab");
  const [treeResult, setTreeResult] = useState(null);
  const [practice, setPractice] = useState(0);
  const [score, setScore] = useState(0);
  const [answers, setAnswers] = useState({});
  const [validateText, setValidateText] = useState("S -> AB | a\nA -> a\nB -> b");
  const [mobileNav, setMobileNav] = useState(false);

  const current = conversion.steps?.[step];
  const validation = useMemo(() => {
    const p = parseGrammar(validateText);
    if (!p.rules.length || p.errors.length) return {valid:false, detail:p.errors.join(" ") || "Enter valid rules."};
    const valid = isCNF(p.rules, p.start);
    return {valid, detail: valid ? "Every production matches a CNF form." : "At least one production violates a CNF rule."};
  }, [validateText]);

  const practiceQuestions = [
    {
      q:"Which production is valid in CNF?",
      options:["A → aB","A → BC","A → BCD","A → ε"],
      correct:1,
      why:"CNF permits A → BC for two non-terminals."
    },
    {
      q:"Which step removes A → B?",
      options:["Binarization","Terminal isolation","Unit-production removal","Parse-tree construction"],
      correct:2,
      why:"A → B is a unit production."
    },
    {
      q:"Which is a valid terminal rule in CNF?",
      options:["A → ab","A → a","A → aB","A → ABC"],
      correct:1,
      why:"A → a is the terminal form allowed by CNF."
    },
    {
      q:"What is the maximum RHS length for a binary CNF production?",
      options:["1","2","3","Unlimited"],
      correct:1,
      why:"The binary form is A → BC."
    },
    {
      q:"Why can a helper variable be introduced for a terminal?",
      options:["To make A → aB legal as A → T B","To delete all terminals","To create ambiguity","To remove the start symbol"],
      correct:0,
      why:"Use T → a, then A → T B."
    }
  ];

  function runConversion() {
    const result = convertCNF(grammar);
    setConversion(result);
    setStep(0);
    setTab("convert");
  }

  function chooseExample(key) {
    setGrammar(EXAMPLES[key].grammar);
    const r = convertCNF(EXAMPLES[key].grammar);
    setConversion(r); setStep(0);
  }

  function answer(i, idx) {
    if (answers[i] !== undefined) return;
    setAnswers(a => ({...a, [i]:idx}));
    if (idx === practiceQuestions[i].correct) setScore(s => s+1);
  }

  if (intro) {
    return (
      <div className="intro-screen">
        <div className="grid-glow"></div>
        <div className="intro-particles">{Array.from({length:35}).map((_,i)=><span key={i} style={{"--i":i}}></span>)}</div>
        <div className="intro-content">
          <div className="eyebrow"><Sparkles size={16}/> FORMAL LANGUAGES • INTERACTIVE LAB</div>
          <h1>CFG <span>→</span> CNF</h1>
          <p>Understand the transformation. See every rule change. Build the parse tree.</p>
          <button className="primary big" onClick={()=>setIntro(false)}><Play size={18}/> Enter Learning Studio</button>
        </div>
      </div>
    );
  }

  return (
    <div className="app">
      <header className="topbar">
        <div className="brand" onClick={()=>setTab("learn")}>
          <div className="brand-mark">CNF</div>
          <div><b>Learning Studio</b><span>CFG → Chomsky Normal Form</span></div>
        </div>
        <button className="mobile-menu" onClick={()=>setMobileNav(v=>!v)}>☰</button>
        <nav className={mobileNav ? "open" : ""}>
          {NAV.map(([id,label,Icon]) => (
            <button key={id} className={tab===id?"active":""} onClick={()=>{setTab(id);setMobileNav(false)}}><Icon size={16}/>{label}</button>
          ))}
        </nav>
      </header>

      <main>
        {tab==="learn" && (
          <section className="page">
            <div className="hero">
              <div>
                <div className="eyebrow"><GraduationCap size={15}/> MASTER CNF STEP BY STEP</div>
                <h2>From a messy grammar<br/><span>to a precise structure.</span></h2>
                <p>CNF is not just a final answer. This studio shows <b>why</b> each transformation is required, what changes, and how the final grammar satisfies the formal definition.</p>
                <div className="hero-actions"><button className="primary" onClick={()=>setTab("convert")}><Zap size={17}/> Start conversion</button><button className="secondary" onClick={()=>setTab("practice")}><Target size={17}/> Test yourself</button></div>
              </div>
              <div className="formula-card">
                <div className="formula-title">CNF RULES</div>
                <div className="formula">A → BC</div>
                <small>two non-terminals</small>
                <div className="formula">A → a</div>
                <small>one terminal</small>
                <div className="formula">S → ε</div>
                <small>only when ε belongs to L(G)</small>
              </div>
            </div>

            <div className="section-title"><span>01</span> What exactly is CNF?</div>
            <div className="cards three">
              <article className="info-card"><Code2/><h3>Formal definition</h3><p>A context-free grammar is in Chomsky Normal Form when every production is either <b>A → BC</b> or <b>A → a</b>, with the special start rule <b>S → ε</b> allowed when needed.</p></article>
              <article className="info-card"><ShieldCheck/><h3>Why convert?</h3><p>CNF gives productions a uniform binary shape. That structure is especially useful for parsing algorithms such as CYK and for proofs about context-free languages.</p></article>
              <article className="info-card"><Lightbulb/><h3>The key idea</h3><p>We do not randomly rewrite rules. Each step removes one kind of obstacle: ε, unit rules, useless symbols, mixed terminals, and RHSs that are too long.</p></article>
            </div>

            <div className="section-title"><span>02</span> What is allowed?</div>
            <div className="rule-grid">
              <div className="good"><CheckCircle2/><b>A → BC</b><span>Valid binary production</span></div>
              <div className="good"><CheckCircle2/><b>A → a</b><span>Valid terminal production</span></div>
              <div className="good"><CheckCircle2/><b>S → ε</b><span>Special case when ε is generated</span></div>
              <div className="bad"><XCircle/><b>A → aB</b><span>Mixed terminal + variable</span></div>
              <div className="bad"><XCircle/><b>A → BCD</b><span>Three variables</span></div>
              <div className="bad"><XCircle/><b>A → B</b><span>Unit production</span></div>
            </div>

            <div className="callout"><Terminal size={18}/><div><b>Memory trick:</b> CNF means “one terminal OR two variables.” If the right side has anything else, another transformation is needed.</div></div>
          </section>
        )}

        {tab==="convert" && (
          <section className="page">
            <div className="page-heading"><div><div className="eyebrow"><Zap size={15}/> CONVERSION ENGINE</div><h2>Watch CFG → CNF happen.</h2><p>Enter a grammar, run the conversion, then move through every transformation.</p></div></div>

            <div className="workspace">
              <aside className="panel editor">
                <div className="panel-head"><span>INPUT CFG</span><span className="hint">Use A -> BC | a</span></div>
                <textarea value={grammar} onChange={e=>setGrammar(e.target.value)} spellCheck="false"/>
                <div className="example-row">
                  {Object.entries(EXAMPLES).map(([k,v])=><button key={k} onClick={()=>chooseExample(k)}>{v.name}</button>)}
                </div>
                <button className="primary full" onClick={runConversion}><Zap size={17}/> Convert to CNF</button>
              </aside>

              <div className="panel result-panel">
                {!conversion.ok && conversion.errors?.length ? (
                  <div className="error-box"><XCircle/><div><b>Fix the grammar</b><p>{conversion.errors.join(" ")}</p></div></div>
                ) : (
                  <>
                    <div className="result-top">
                      <div><span className="status-dot"></span> CNF result ready</div>
                      <span className="badge">START: {conversion.start}</span>
                    </div>
                    <pre className="grammar-box">{formatRules(conversion.final)}</pre>
                    <div className="cnf-proof"><CheckCircle2/><div><b>Verified CNF</b><span>Every final production matches A → BC, A → a, or the permitted start ε-rule.</span></div></div>
                  </>
                )}
              </div>
            </div>

            {conversion.steps?.length > 0 && (
              <>
                <div className="section-title"><span>03</span> Step-by-step transformation</div>
                <div className="stepper">
                  {conversion.steps.map((s,i)=><button key={i} className={i===step?"current":i<step?"done":""} onClick={()=>setStep(i)}><span>{i+1}</span><b>{s.title}</b></button>)}
                </div>
                <div className="step-detail">
                  <div className="step-title-row"><div><div className="eyebrow">{current.subtitle}</div><h3>{current.title}</h3></div><div className="step-controls"><button disabled={step===0} onClick={()=>setStep(s=>s-1)}><ChevronLeft/></button><button disabled={step===conversion.steps.length-1} onClick={()=>setStep(s=>s+1)}><ChevronRight/></button></div></div>
                  <div className="why"><Lightbulb/><div><b>Why this step?</b><p>{current.why}</p></div></div>
                  <div className="compare">
                    <div><label>BEFORE</label><pre>{formatRules(current.before)}</pre></div>
                    <div className="arrow">→</div>
                    <div><label>AFTER</label><pre>{formatRules(current.after)}</pre></div>
                  </div>
                </div>
                <div className="callout"><CheckCircle2 size={18}/><div><b>How to study this:</b> Compare only the rules that changed. Ask yourself: “Which CNF restriction did this step fix?” Then move to the next stage.</div></div>
              </>
            )}
          </section>
        )}

        {tab==="tree" && (
          <section className="page">
            <div className="page-heading"><div><div className="eyebrow"><GitBranch size={15}/> PARSE TREE VISUALIZER</div><h2>See how a string is derived.</h2><p>Enter a CFG and a string. The visualizer searches for a derivation and draws the tree.</p></div></div>
            <div className="workspace tree-workspace">
              <aside className="panel editor">
                <div className="panel-head"><span>GRAMMAR</span></div>
                <textarea value={treeGrammar} onChange={e=>setTreeGrammar(e.target.value)} spellCheck="false"/>
                <label className="field-label">STRING</label>
                <input value={treeInput} onChange={e=>setTreeInput(e.target.value)} />
                <button className="primary full" onClick={()=>setTreeResult(buildParseTree(treeGrammar, treeInput))}><GitBranch size={17}/> Generate parse tree</button>
              </aside>
              <div className="panel tree-panel">
                {!treeResult && <div className="empty"><GitBranch size={42}/><h3>Parse tree will appear here</h3><p>Try S → AB, A → a, B → b with input “ab”.</p></div>}
                {treeResult && !treeResult.ok && <div className="error-box"><XCircle/><div><b>No derivation</b><p>{treeResult.message}</p></div></div>}
                {treeResult?.ok && <div className="tree-canvas"><div className="tree-title">DERIVATION TREE</div><TreeNode node={treeResult.tree}/><div className="yield"><span>YIELD</span>{treeResult.input}</div></div>}
              </div>
            </div>
            <div className="cards three">
              <article className="info-card"><GitBranch/><h3>Root</h3><p>The root is the grammar's start symbol.</p></article>
              <article className="info-card"><Terminal/><h3>Leaves</h3><p>Terminal symbols appear at the bottom and spell the generated string.</p></article>
              <article className="info-card"><Sparkles/><h3>Connection to CNF</h3><p>In CNF, internal binary nodes naturally have two children, which is why CNF is convenient for CYK parsing.</p></article>
            </div>
          </section>
        )}

        {tab==="practice" && (
          <section className="page">
            <div className="page-heading"><div><div className="eyebrow"><Target size={15}/> PRACTICE MODE</div><h2>Prove you understand it.</h2><p>Five questions. Immediate feedback. Your score updates as you answer.</p></div><div className="score-card"><span>SCORE</span><b>{score}/{practiceQuestions.length}</b></div></div>
            <div className="progress-line"><div style={{width:`${Object.keys(answers).length/practiceQuestions.length*100}%`}}></div></div>
            <div className="practice-list">
              {practiceQuestions.map((q,i)=>{
                const selected=answers[i];
                return <article className="question" key={i}>
                  <div className="q-number">Q{i+1}</div><h3>{q.q}</h3>
                  <div className="options">{q.options.map((o,j)=><button disabled={selected!==undefined} className={selected===j ? (j===q.correct?"correct":"wrong") : (selected!==undefined&&j===q.correct?"correct":"")} onClick={()=>answer(i,j)} key={j}><span>{String.fromCharCode(65+j)}</span>{o}</button>)}</div>
                  {selected!==undefined && <div className={`feedback ${selected===q.correct?"success":"fail"}`}>{selected===q.correct?<CheckCircle2/>:<XCircle/>}<div><b>{selected===q.correct?"Correct!":"Not quite."}</b><p>{q.why}</p></div></div>}
                </article>
              })}
            </div>
            <button className="secondary" onClick={()=>{setAnswers({});setScore(0)}}><RotateCcw size={16}/> Reset practice</button>
          </section>
        )}

        {tab==="validate" && (
          <section className="page">
            <div className="page-heading"><div><div className="eyebrow"><ShieldCheck size={15}/> CNF VALIDATOR</div><h2>Check a grammar rule-by-rule.</h2><p>The validator checks the structural CNF forms directly.</p></div></div>
            <div className="validator">
              <div className="panel editor"><div className="panel-head"><span>GRAMMAR</span></div><textarea value={validateText} onChange={e=>setValidateText(e.target.value)} spellCheck="false"/></div>
              <div className={`validation-result ${validation.valid?"valid":"invalid"}`}>{validation.valid?<CheckCircle2/>:<XCircle/>}<h3>{validation.valid?"Valid CNF":"Not CNF"}</h3><p>{validation.detail}</p>
                <div className="checklist"><div><b>✓</b> A → BC — two variables</div><div><b>✓</b> A → a — one terminal</div><div><b>✓</b> S → ε — special start case</div><div><b>×</b> A → B — unit production</div><div><b>×</b> A → aB — mixed symbols</div><div><b>×</b> A → ABC — too many variables</div></div>
              </div>
            </div>
          </section>
        )}
      </main>

      <footer><span>CNF Learning Studio</span><span>Built for learning formal languages • React + Vite</span></footer>
    </div>
  );
}

createRoot(document.getElementById("root")).render(<App />);
