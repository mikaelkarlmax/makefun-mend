// main.ts is mend, the CLI SPEC.md specifies, and this is the kit's starting point for it (MIT). It does sections 1 to 4, 9 and 10 of SPEC.md: the command line, the output and
// exit codes, safe paths, format detection, JSON edits and the all-or-nothing write. The other three formats are
// detected and then read as holding no edit, so they answer `error: parse 1`: reading unified diffs (section 6),
// SEARCH/REPLACE blocks (section 7) and V4A patches (section 8), and matching lines at three tiers (section 5), are
// yours to write. Node 22, the standard library alone; run it as `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to runner.ts
// (the last lines below): keep that hand-over and runner.ts as they are, and write the CLI.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

interface FileState {
  lines: string[];
  br: string;
  final: boolean;
}

function parseFile(text: string): FileState {
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  if (text === '') return { lines: [], br, final: false };
  const lines = text.split(br);
  const final = text.endsWith(br);
  if (final) lines.pop();
  return { lines, br, final };
}

function serializeFile(f: FileState): string {
  return f.lines.length === 0 ? '' : f.lines.join(f.br) + (f.final ? f.br : '');
}

const leadWS = (s: string): string => /^[ \t]*/.exec(s)![0];
const rstripWS = (s: string): string => s.replace(/[ \t]+$/, '');
const stripWS = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');

function lineMatches(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return rstripWS(a) === rstripWS(b);
  return stripWS(a) === stripWS(b);
}

function occurrences(lines: string[], o: string[], tier: number, from = 0): number[] {
  const out: number[] = [];
  for (let i = from; i + o.length <= lines.length; i += 1) {
    let ok = true;
    for (let k = 0; k < o.length; k += 1) {
      if (!lineMatches(lines[i + k]!, o[k]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier at which o occurs in lines (at or after `from`), with its positions there. */
function findTier(lines: string[], o: string[], strict: boolean, from = 0): { tier: number; positions: number[] } | null {
  const top = strict ? 0 : 2;
  for (let tier = 0; tier <= top; tier += 1) {
    const positions = occurrences(lines, o, tier, from);
    if (positions.length > 0) return { tier, positions };
  }
  return null;
}

function reindent(line: string, p: string, f: string): string {
  if (line !== '' && line.trim() !== '' && line.startsWith(p)) return f + line.slice(p.length);
  return line;
}

interface BodyEntry {
  kind: string;
  text: string;
  blankLine?: boolean;
}

/** Replacement lines for matched O: context lines come from the file, `+` lines from the patch. */
function buildReplacement(body: BodyEntry[], fileLines: string[], pos: number, tier: number, o: string[]): string[] {
  const p = o.length > 0 ? leadWS(o[0]!) : '';
  const f = o.length > 0 ? leadWS(fileLines[pos]!) : '';
  const out: string[] = [];
  let oi = 0;
  for (const e of body) {
    if (e.kind === ' ') {
      out.push(fileLines[pos + oi]!);
      oi += 1;
    } else if (e.kind === '-') {
      oi += 1;
    } else if (e.kind === '+') {
      out.push(tier === 2 ? reindent(e.text, p, f) : e.text);
    }
  }
  return out;
}

/** Whether a `\` line follows the body's last context or `+` line. */
function backslashAfterLast(body: BodyEntry[]): boolean {
  let idx = -1;
  for (let i = 0; i < body.length; i += 1) {
    if (body[i]!.kind === ' ' || body[i]!.kind === '+') idx = i;
  }
  if (idx < 0) idx = body.length - 1;
  return idx >= 0 && body[idx + 1]?.kind === '\\';
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: Array<[string, string]> = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

interface UHunk {
  a: number;
  body: BodyEntry[];
}

function applyUnifiedHunks(state: FileState, hunks: UHunk[], strict: boolean, path: string): FileState {
  const lines = [...state.lines];
  let fin = state.final;
  let d = 0;
  for (const hunk of hunks) {
    const o = hunk.body.filter((e) => e.kind === ' ' || e.kind === '-').map((e) => e.text);
    const nEntries = hunk.body.filter((e) => e.kind === ' ' || e.kind === '+');
    if (o.length === 0) {
      const at = Math.max(0, Math.min(hunk.a + d, lines.length));
      const repl = nEntries.map((e) => e.text);
      const atEnd = at === lines.length;
      lines.splice(at, 0, ...repl);
      if (atEnd) fin = !backslashAfterLast(hunk.body);
      d += repl.length;
      continue;
    }
    const found = findTier(lines, o, strict);
    if (found === null) throw new Fail('no-match', path);
    const target = hunk.a - 1 + d;
    let pos = found.positions[0]!;
    for (const cand of found.positions) {
      if (Math.abs(cand - target) < Math.abs(pos - target)) pos = cand;
    }
    const repl = buildReplacement(hunk.body, lines, pos, found.tier, o);
    const atEnd = pos + o.length === lines.length;
    lines.splice(pos, o.length, ...repl);
    if (atEnd) fin = !backslashAfterLast(hunk.body);
    d += nEntries.length - o.length;
  }
  return { lines, br: state.br, final: fin };
}

interface USection {
  oldP: string | null;
  newP: string | null;
  diffOld: string | null;
  diffNew: string | null;
  renameFrom: string | null;
  renameTo: string | null;
  newFile: boolean;
  delFile: boolean;
  hunks: UHunk[];
}

function newUSection(): USection {
  return { oldP: null, newP: null, diffOld: null, diffNew: null, renameFrom: null, renameTo: null, newFile: false, delFile: false, hunks: [] };
}

function headerPath(raw: string): string {
  const p = raw.split('\t')[0]!.trim();
  if (p === '/dev/null') return p;
  return p.startsWith('a/') || p.startsWith('b/') ? p.slice(2) : p;
}

function unifiedSectionEdit(sec: USection, strict: boolean): Edit {
  const oldP = sec.oldP ?? sec.renameFrom ?? sec.diffOld;
  const newP = sec.newP ?? sec.renameTo ?? sec.diffNew;
  const isCreate = oldP === '/dev/null' || sec.newFile;
  const isDelete = newP === '/dev/null' || sec.delFile;
  return (tree) => {
    if (isCreate) {
      const target = newP!;
      if (!safe(target)) throw new Fail('unsafe', target);
      if (tree.get(target) !== null) throw new Fail('exists', target);
      const flat = sec.hunks.flatMap((h) => h.body);
      const plus = flat.filter((e) => e.kind === '+').map((e) => e.text);
      let fin = true;
      for (let i = flat.length - 1; i >= 0; i -= 1) {
        if (flat[i]!.kind === '+') {
          fin = flat[i + 1]?.kind !== '\\';
          break;
        }
      }
      tree.now.set(target, plus.length === 0 ? '' : plus.join('\n') + (fin ? '\n' : ''));
      return;
    }
    if (isDelete) {
      const target = oldP!;
      if (!safe(target)) throw new Fail('unsafe', target);
      if (tree.get(target) === null) throw new Fail('missing', target);
      tree.now.set(target, null);
      return;
    }
    if (oldP !== null && newP !== null && oldP !== newP) {
      if (!safe(oldP)) throw new Fail('unsafe', oldP);
      if (!safe(newP)) throw new Fail('unsafe', newP);
      const before = tree.get(oldP);
      if (before === null) throw new Fail('missing', oldP);
      if (tree.get(newP) !== null) throw new Fail('exists', newP);
      const out = applyUnifiedHunks(parseFile(before), sec.hunks, strict, oldP);
      tree.now.set(oldP, null);
      tree.now.set(newP, serializeFile(out));
      tree.moves.push([oldP, newP]);
      return;
    }
    const target = (oldP ?? newP)!;
    if (!safe(target)) throw new Fail('unsafe', target);
    const before = tree.get(target);
    if (before === null) throw new Fail('missing', target);
    const out = applyUnifiedHunks(parseFile(before), sec.hunks, strict, target);
    tree.now.set(target, serializeFile(out));
  };
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections: USection[] = [];
  let cur: USection | null = null;
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(.+) b\/(.+)$/.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      cur = newUSection();
      cur.diffOld = m[1]!;
      cur.diffNew = m[2]!;
      sections.push(cur);
      i += 1;
      continue;
    }
    if (line.startsWith('--- ')) {
      const next = lines[i + 1] ?? '';
      if (next.startsWith('+++ ')) {
        if (cur === null || cur.hunks.length > 0 || cur.oldP !== null) {
          cur = newUSection();
          sections.push(cur);
        }
        cur.oldP = headerPath(line.slice(4));
        cur.newP = headerPath(next.slice(4));
        i += 2;
        continue;
      }
      if (cur !== null && cur.hunks.length === 0) throw new Exit2(`error: parse ${i + 2}`);
      i += 1;
      continue;
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const m = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      const body: BodyEntry[] = [];
      let j = i + 1;
      while (j < lines.length) {
        const l = lines[j]!;
        if (l.startsWith('diff --git ')) break;
        if (l.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
        if (l === '') {
          body.push({ kind: ' ', text: '', blankLine: true });
          j += 1;
          continue;
        }
        const c = l[0]!;
        if (c === ' ' || c === '-' || c === '+' || c === '\\') {
          body.push({ kind: c, text: l.slice(1) });
          j += 1;
          continue;
        }
        break;
      }
      while (body.length > 0 && body[body.length - 1]!.blankLine === true) body.pop();
      cur.hunks.push({ a: Number(m[1]), body });
      i = j;
      continue;
    }
    if (cur !== null && cur.hunks.length === 0) {
      if (line.startsWith('rename from ')) cur.renameFrom = line.slice(12);
      else if (line.startsWith('rename to ')) cur.renameTo = line.slice(10);
      else if (line.startsWith('new file mode')) cur.newFile = true;
      else if (line.startsWith('deleted file mode')) cur.delFile = true;
    }
    i += 1;
  }
  return sections.map((s) => unifiedSectionEdit(s, strict));
}

function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevPath: string | null = null;
  let regionStart = 0;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i += 1;
      continue;
    }
    const searchLine = i;
    let path: string | null = null;
    for (let k = searchLine - 1; k >= regionStart; k -= 1) {
      const l = lines[k]!;
      if (blank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) path = prevPath;
    if (path === null) throw new Exit2(`error: parse ${searchLine + 1}`);
    let eq = -1;
    for (let k = searchLine + 1; k < lines.length; k += 1) {
      if (lines[k]!.trimEnd() === '=======') {
        eq = k;
        break;
      }
    }
    let rep = -1;
    if (eq >= 0) {
      for (let k = eq + 1; k < lines.length; k += 1) {
        if (lines[k]!.trimEnd() === '>>>>>>> REPLACE') {
          rep = k;
          break;
        }
      }
    }
    if (eq < 0 || rep < 0) throw new Exit2(`error: parse ${searchLine + 1}`);
    const oldLines = lines.slice(searchLine + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    const p = path;
    edits.push((tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (oldLines.length === 0) {
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
        return;
      }
      const before = tree.get(p);
      if (before === null) throw new Fail('missing', p);
      const state = parseFile(before);
      const found = findTier(state.lines, oldLines, strict);
      if (found === null) throw new Fail('no-match', p);
      if (found.positions.length > 1) throw new Fail('ambiguous', p);
      const pos = found.positions[0]!;
      const indentP = leadWS(oldLines[0]!);
      const indentF = leadWS(state.lines[pos]!);
      const repl = newLines.map((l) => (found.tier === 2 ? reindent(l, indentP, indentF) : l));
      state.lines.splice(pos, oldLines.length, ...repl);
      tree.now.set(p, serializeFile(state));
    });
    prevPath = p;
    regionStart = rep + 1;
    i = rep + 1;
  }
  return edits;
}

interface VChunk {
  anchor: string | null;
  body: BodyEntry[];
  eof: boolean;
}

function applyVChunk(state: FileState, chunk: VChunk, cursor: number, strict: boolean, path: string): number {
  const lines = state.lines;
  if (chunk.anchor !== null) {
    const anchor = chunk.anchor;
    let at = -1;
    const top = strict ? 0 : 2;
    for (let tier = 0; tier <= top && at < 0; tier += 1) {
      for (let k = cursor; k < lines.length; k += 1) {
        if (lineMatches(lines[k]!, anchor, tier)) {
          at = k;
          break;
        }
      }
    }
    if (at < 0) throw new Fail('no-match', path);
    cursor = at + 1;
  }
  const o = chunk.body.filter((e) => e.kind === ' ' || e.kind === '-').map((e) => e.text);
  const nEntries = chunk.body.filter((e) => e.kind === ' ' || e.kind === '+');
  if (o.length === 0) {
    const at = chunk.eof ? lines.length : Math.min(cursor, lines.length);
    const repl = nEntries.map((e) => e.text);
    lines.splice(at, 0, ...repl);
    return at + repl.length;
  }
  const top = strict ? 0 : 2;
  let chosen: { tier: number; pos: number } | null = null;
  for (let tier = 0; tier <= top && chosen === null; tier += 1) {
    for (const pos of occurrences(lines, o, tier, cursor)) {
      if (chunk.eof && pos + o.length !== lines.length) continue;
      chosen = { tier, pos };
      break;
    }
  }
  if (chosen === null) throw new Fail('no-match', path);
  const repl = buildReplacement(chunk.body, lines, chosen.pos, chosen.tier, o);
  lines.splice(chosen.pos, o.length, ...repl);
  return chosen.pos + repl.length;
}

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k -= 1) {
    if (!blank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  const sectionStart = (l: string): { kind: string; path: string } | null => {
    for (const [prefix, kind] of [['*** Add File: ', 'add'], ['*** Delete File: ', 'delete'], ['*** Update File: ', 'update']] as const) {
      if (l.startsWith(prefix)) return { kind, path: l.slice(prefix.length).trim() };
    }
    return null;
  };
  let i = first + 1;
  while (i < last) {
    if (blank(lines[i]!)) {
      i += 1;
      continue;
    }
    const head = sectionStart(lines[i]!);
    if (head === null) throw new Exit2(`error: parse ${i + 1}`);
    const headLine = i + 1;
    const raw: Array<{ line: string; num: number }> = [];
    let j = i + 1;
    while (j < last && sectionStart(lines[j]!) === null) {
      raw.push({ line: lines[j]!, num: j + 1 });
      j += 1;
    }
    while (raw.length > 0 && blank(raw[raw.length - 1]!.line)) raw.pop();
    const p = head.path;
    if (head.kind === 'add') {
      const content: string[] = [];
      for (const r of raw) {
        if (r.line.startsWith('+')) content.push(r.line.slice(1));
        else if (r.line === '') content.push('');
        else throw new Exit2(`error: parse ${r.num}`);
      }
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, content.length === 0 ? '' : content.join('\n') + '\n');
      });
    } else if (head.kind === 'delete') {
      if (raw.length > 0) throw new Exit2(`error: parse ${raw[0]!.num}`);
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
      });
    } else {
      let moveTo: string | null = null;
      let start = 0;
      if (raw.length > 0 && raw[0]!.line.startsWith('*** Move to: ')) {
        moveTo = raw[0]!.line.slice('*** Move to: '.length).trim();
        start = 1;
      }
      const chunks: VChunk[] = [];
      let cur: VChunk | null = null;
      for (let k = start; k < raw.length; k += 1) {
        const r = raw[k]!;
        if (r.line.startsWith('@@')) {
          const anchor = r.line.slice(2).trim();
          cur = { anchor: anchor === '' ? null : anchor, body: [], eof: false };
          chunks.push(cur);
        } else if (r.line === '*** End of File') {
          if (cur === null) {
            cur = { anchor: null, body: [], eof: false };
            chunks.push(cur);
          }
          cur.eof = true;
          cur = null;
        } else if (r.line === '' || r.line[0] === ' ' || r.line[0] === '-' || r.line[0] === '+') {
          if (cur === null) {
            cur = { anchor: null, body: [], eof: false };
            chunks.push(cur);
          }
          cur.body.push(r.line === '' ? { kind: ' ', text: '' } : { kind: r.line[0]!, text: r.line.slice(1) });
        } else {
          throw new Exit2(`error: parse ${r.num}`);
        }
      }
      if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${headLine}`);
      const mv = moveTo;
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (mv !== null && !safe(mv)) throw new Fail('unsafe', mv);
        const before = tree.get(p);
        if (before === null) throw new Fail('missing', p);
        if (mv !== null && tree.get(mv) !== null) throw new Fail('exists', mv);
        const state = parseFile(before);
        let cursor = 0;
        for (const chunk of chunks) cursor = applyVChunk(state, chunk, cursor, strict, p);
        if (mv !== null) {
          tree.now.set(p, null);
          tree.now.set(mv, serializeFile(state));
          tree.moves.push([p, mv]);
        } else {
          tree.now.set(p, serializeFile(state));
        }
      });
    }
    i = j;
  }
  return edits;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    edits =
      kind === 'json'
        ? jsonEdits(text, lines)
        : kind === 'unified'
          ? unifiedEdits(lines, strict)
          : kind === 'search-replace'
            ? searchReplaceEdits(lines, strict)
            : v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const moveNew = new Map<string, string>();
  const moveOld = new Set<string>();
  for (const [o, n] of tree.moves) {
    if (tree.original(o) !== null && tree.get(o) === null && tree.original(n) === null && tree.get(n) !== null) {
      moveNew.set(n, o);
      moveOld.add(o);
    }
  }
  const rows: string[] = [];
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (!moveOld.has(p)) rows.push(moveNew.has(p) ? `R ${moveNew.get(p)!} -> ${p}` : `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}`);
    if (check) continue;
    if (now === null) rmSync(p, { force: true });
    else {
      mkdirSync(dirname(p), { recursive: true });
      writeFileSync(p, now);
    }
  }
  return { code: 0, out: [...rows, `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}


const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
