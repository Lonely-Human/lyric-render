"use strict";
// Worker untuk GitHub Actions: download payload + audio + cover dari CDN,
// render video, lalu upload hasilnya ke CDN.
const fs = require("fs");
const fsp = fs.promises;
const path = require("path");
const os = require("os");

async function main() {
  const payloadUrl = process.env.LYRIC_JOB_URL;
  const cdnApi = process.env.CDN_API_BASE_URL || "https://cdn.patrickbotz.com";
  const cdnKey = process.env.CDN_API_KEY || "";
  if (!payloadUrl) throw new Error("LYRIC_JOB_URL kosong");

  const res = await fetch(payloadUrl);
  if (!res.ok) throw new Error("Gagal unduh payload: HTTP " + res.status);
  const job = await res.json();

  const dir = await fsp.mkdtemp(path.join(os.tmpdir(), "lyric-job-"));
  const audioPath = path.join(dir, "audio" + (path.extname(job.audioUrl) || ".m4a"));
  const coverPath = path.join(dir, "cover.jpg");

  for (const [url, dest] of [[job.audioUrl, audioPath], [job.coverUrl, coverPath]]) {
    const r = await fetch(url);
    if (!r.ok) throw new Error("Gagal unduh " + url + ": HTTP " + r.status);
    await fsp.writeFile(dest, Buffer.from(await r.arrayBuffer()));
  }

  const lyric = require("./lib/lyric-video2");
  const outPath = path.join(dir, "lyric-video.mp4");
  await lyric.renderLyricVideoJob(job, audioPath, coverPath, outPath);

  const buffer = await fsp.readFile(outPath);
  const form = new FormData();
  form.append("file", new Blob([buffer], { type: "video/mp4" }), job.jobId + ".mp4");
  const up = await fetch(cdnApi + "/v1/upload", {
    method: "POST",
    headers: { Authorization: "Bearer " + cdnKey },
    body: form,
  });
  const upText = await up.text();
  let upData = {};
  try { upData = JSON.parse(upText); } catch (_) {}
  if (!up.ok || !upData.url) throw new Error("Gagal upload hasil: " + upText.slice(0, 200));
  console.log("RESULT_URL=" + upData.url);
  await fsp.rm(dir, { recursive: true, force: true }).catch(() => {});
}

main().catch((e) => { console.error(e); process.exit(1); });
