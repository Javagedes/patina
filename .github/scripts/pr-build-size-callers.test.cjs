// Copyright (c) Microsoft Corporation.
// SPDX-License-Identifier: Apache-2.0
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const { test } = require('node:test');

const headSha = 'b'.repeat(40);
const baseSha = 'a'.repeat(40);
const sourceRepo = 'contributor/patina';
const sourceRef = 'test-size';
const workflow = name => fs.readFileSync(path.join(__dirname, '..', 'workflows', name), 'utf8').replaceAll('\r\n', '\n');
const pr = {
  number: 42, state: 'open', merged_at: null,
  head: { sha: headSha, ref: sourceRef, repo: { full_name: sourceRepo } },
  base: { sha: baseSha, ref: 'main' },
};

async function resolve({ open = [pr], closed = [], associated = [], env = {}, owner = 'OpenDevicePartnership' } = {}) {
  const step = workflow('patina-pr-build-size.yml').split('      - name: Get PR Information\n')[1]
    .split('\n      - name: ')[0];
  const script = /\n          script: \|\n((?:            [^\n]*(?:\n|$)|\n)*)/.exec(step)[1]
    .split('\n').map(line => line.replace(/^            /, '')).join('\n');
  const AsyncFunction = Object.getPrototypeOf(async function () {}).constructor;
  const collect = new AsyncFunction('github', 'context', 'core', 'process', script);
  const outputs = {};
  const queries = [];
  const notices = [];
  const logs = [];
  const list = Symbol('pulls.list');
  await collect({
    rest: { pulls: { list } },
    paginate: async (method, query) => {
      assert.equal(method, list);
      queries.push(query);
      return query.state === 'open' ? open : closed;
    },
  }, {
    repo: { owner, repo: 'patina' },
    sha: 'd'.repeat(40),
    payload: { workflow_run: { pull_requests: associated.map(number => ({ number })) } },
  }, {
    setOutput: (key, value) => { outputs[key] = value; },
    notice: message => notices.push(message),
    info: message => logs.push(message),
    startGroup: () => {}, endGroup: () => {},
  }, {
    env: {
      SOURCE_RUN_ID: '100', HEAD_SHA: headSha, HEAD_REF: sourceRef, HEAD_REPO: sourceRepo, ...env,
    },
  });
  return { outputs, queries, notices, logs };
}

test('caller waits for successful PR CI before preparing metadata or invoking the reusable workflow', () => {
  const build = workflow('patina-pr-build-size.yml');
  const post = workflow('patina-pr-build-size-post.yml');
  assert.match(build, /on:\n  workflow_run:\n    workflows: \["CI"\]/);
  assert.ok(build.includes("github.event.workflow_run.conclusion == 'success'"));
  assert.ok(build.includes("github.event.workflow_run.event == 'pull_request'"));
  assert.ok(build.includes("needs.prepare.result == 'success' && needs.prepare.outputs.skip == 'false'"));
  assert.ok(build.includes('uses: Javagedes/patina-devops/.github/workflows/PatinaPrBuildSize.yml@feature/pr-size-workflow'));
  assert.ok(build.includes('base-sha: ${{ needs.prepare.outputs.base_sha }}'));
  assert.ok(build.includes('head-sha: ${{ github.event.workflow_run.head_sha }}'));
  const buildJob = build.split('\n  build-size:\n')[1];
  assert.deepEqual([...buildJob.matchAll(/^      ([\w-]+):/gm)].map(match => match[1]),
    ['base-sha', 'head-sha']);
  assert.ok(build.includes('name: patina-build-size-pr-metadata'));
  assert.ok(build.indexOf('      - name: Upload PR Metadata') < build.indexOf('  build-size:'));
  assert.doesNotMatch(build, /uses: actions\/checkout@/);
  assert.ok(post.includes('uses: Javagedes/patina-devops/.github/workflows/PatinaPrBuildSizePost.yml@feature/pr-size-workflow'));
  assert.ok(post.includes('triggering-run-id: ${{ github.event.workflow_run.id }}'));
  assert.ok(post.includes("github.event.workflow_run.event == 'workflow_run'"));
  assert.ok(build.includes('run-name: Patina PR Build Size - ${{ github.event.workflow_run.head_repository.full_name }}:'));
  assert.ok(post.includes('group: pr-build-size-post-${{ github.event.workflow_run.display_title }}'));
  assert.doesNotMatch(post, /\bsteps:/);
});

test('caller freezes the target SHA and records CI PR identity, refs, and source', async () => {
  const { outputs, queries, logs } = await resolve();
  assert.deepEqual(outputs, {
    base_sha: baseSha, skip: false,
    metadata: {
      source_run_id: 100, pr_number: 42, head_sha: headSha, base_sha: baseSha, base_ref: 'main',
      skipped: false, skip_reason: '',
    },
  });
  assert.deepEqual(queries, [{
    owner: 'OpenDevicePartnership', repo: 'patina', head: 'contributor:test-size', per_page: 100, state: 'open',
  }]);
  for (const value of [headSha, baseSha, sourceRef, sourceRepo, 'main']) {
    assert.ok(logs.some(message => message.includes(value)));
  }
});

test('caller supports feature targets and uses CI PR associations to disambiguate a shared source branch', async () => {
  const target = { ...pr, base: { sha: baseSha, ref: 'feature/nested/core' } };
  const { outputs, logs } = await resolve({ open: [{ ...pr, number: 43 }, target], associated: [42] });
  assert.equal(outputs.metadata.pr_number, 42);
  assert.equal(outputs.base_sha, baseSha);
  assert.equal(outputs.metadata.base_ref, 'feature/nested/core');
  assert.ok(logs.includes('Base Ref: feature/nested/core'));
  assert.equal(outputs.skip, false);
});

test('caller discovers PRs in the personal fork instead of the upstream repository', async () => {
  const { outputs, queries } = await resolve({
    owner: 'Javagedes', env: { HEAD_REPO: 'Javagedes/patina' },
    open: [{ ...pr, head: { ...pr.head, repo: { full_name: 'Javagedes/patina' } } }],
  });
  assert.equal(queries[0].owner, 'Javagedes');
  assert.equal(queries[0].repo, 'patina');
  assert.equal(queries[0].head, `Javagedes:${sourceRef}`);
  assert.equal(outputs.base_sha, baseSha);
  assert.equal(outputs.skip, false);
});

test('caller skips obsolete heads and unsupported target branches before compilation', async () => {
  for (const [current, reason] of [
    [{ ...pr, head: { ...pr.head, sha: 'c'.repeat(40) } }, 'outdated_head'],
    [{ ...pr, base: { sha: baseSha, ref: 'major' } }, 'unsupported_target_branch'],
  ]) {
    const { outputs, notices } = await resolve({ open: [current] });
    assert.equal(outputs.skip, true);
    assert.equal(outputs.metadata.skip_reason, reason);
    assert.equal(outputs.metadata.skipped, true);
    assert.equal(outputs.metadata.head_sha, headSha);
    assert.ok(notices[0].includes(reason));
  }
});

test('caller identifies closed and merged PRs and preserves skip metadata', async () => {
  for (const [merged, reason] of [[null, 'closed'], ['2026-10-19T00:00:00Z', 'merged']]) {
    const { outputs, queries } = await resolve({
      open: [], closed: [{ ...pr, state: 'closed', merged_at: merged }],
    });
    assert.equal(outputs.metadata.pr_number, 42);
    assert.equal(outputs.skip, true);
    assert.equal(outputs.metadata.skip_reason, reason);
    assert.equal(queries[1].state, 'closed');
    assert.equal(queries[1].sort, 'updated');
    assert.equal(queries[1].direction, 'desc');
  }
});

test('caller skips missing sources and does not select PRs from a different fork', async () => {
  for (const options of [
    { open: [], closed: [] },
    { open: [{ ...pr, head: { ...pr.head, repo: { full_name: 'someone-else/patina' } } }] },
    { env: { HEAD_REPO: '' } },
  ]) {
    const { outputs, notices } = await resolve(options);
    assert.equal(outputs.skip, true);
    assert.equal(outputs.metadata.skip_reason, 'branch_unavailable');
    assert.equal(outputs.base_sha, '');
    assert.equal(outputs.metadata.pr_number, null);
    assert.equal(notices.length, 1);
  }
});

test('caller rejects invalid source CI identity explicitly', async () => {
  for (const env of [{ SOURCE_RUN_ID: '0' }, { HEAD_SHA: 'main' }, { HEAD_REF: '' }]) {
    await assert.rejects(resolve({ env }), /valid source CI run/);
  }
});
