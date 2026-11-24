// node --test .github/scripts/locked-lake.test.mjs
// THE LOCKED BUILD stays locked: every build of an outside file on this runner goes through
// .github/scripts/lake-locked.sh (the locked account, no credential of this run). The checker
// wrapper must never choose its own lake, and the workflow must hand it the locked one.
// (Operator's rehearsal, 2026-11-24: a fleet wrapper that set PEQUALNP_REAL_LAKE itself was copied
// here by mistake and would have built outside Lean as the workflow's account.)
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
const root = new URL('../../', import.meta.url);
const wrapper = readFileSync(new URL('tools/check-lean.mjs', root), 'utf8');
const workflow = readFileSync(new URL('.github/workflows/authoritative.yml', root), 'utf8');
test('the checker wrapper never sets the lake it builds with', () => {
  assert.doesNotMatch(wrapper, /PEQUALNP_REAL_LAKE\s*=|\[\s*['"]PEQUALNP_REAL_LAKE['"]\s*\]\s*=/, 'tools/check-lean.mjs assigns PEQUALNP_REAL_LAKE');
  assert.doesNotMatch(wrapper, /\bREAL_LAKE\b/, 'tools/check-lean.mjs names a REAL_LAKE of its own');
});
test('the workflow runs the checker with the locked lake', () => {
  assert.match(workflow, /PEQUALNP_REAL_LAKE="\$W\/base\/\.github\/scripts\/lake-locked\.sh"[^\n]*\\\n(?:[^\n]*\\\n)*[^\n]*node "\$W\/base\/tools\/check-lean\.mjs"/, 'the check-lean.mjs call is not given lake-locked.sh as its lake');
});
