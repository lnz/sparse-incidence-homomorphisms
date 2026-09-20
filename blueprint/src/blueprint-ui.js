document.addEventListener("DOMContentLoaded", () => {
  const header = document.querySelector("body > header");
  const toggle = document.getElementById("toc-toggle");
  const toc = document.querySelector("nav.toc");

  if (header) {
    const brand = document.createElement("a");
    brand.className = "site-brand";
    brand.href = "index.html";
    brand.textContent = "Theorem 1.1";
    header.insertBefore(brand, document.getElementById("doc_title"));
  }

  if (toggle && toc) {
    toggle.setAttribute("role", "button");
    toggle.setAttribute("tabindex", "0");
    toggle.setAttribute("aria-label", "Toggle contents");
    toggle.setAttribute("aria-controls", "blueprint-contents");
    toc.id = "blueprint-contents";

    const label = document.createElement("span");
    label.className = "toc-toggle-label";
    label.textContent = "Contents";
    toggle.after(label);
    label.addEventListener("click", () => toggle.dispatchEvent(new MouseEvent("click", { bubbles: true })));
    toggle.addEventListener("keydown", (event) => {
      if (event.key === "Enter" || event.key === " ") {
        event.preventDefault();
        toggle.dispatchEvent(new MouseEvent("click", { bubbles: true }));
      }
    });
  }

  const homeTheorem = document.querySelector('div[class*="homepagewidth_thmwrapper"]');
  if (homeTheorem) document.body.classList.add("blueprint-home");

  const main = document.querySelector(".main-text");
  if (main && !homeTheorem) {
    const statements = [...main.querySelectorAll('div[class*="_thmwrapper"][id]')];
    if (statements.length > 1) {
      const index = document.createElement("details");
      index.className = "section-index";
      index.open = true;
      const summary = document.createElement("summary");
      summary.textContent = "In this section";
      const count = document.createElement("span");
      count.textContent = `${statements.length} statements`;
      summary.append(count);
      const list = document.createElement("ul");
      for (const statement of statements) {
        const caption = statement.querySelector('[class$="_thmcaption"]')?.textContent.trim() || "Statement";
        const number = statement.querySelector('[class$="_thmlabel"]')?.textContent.trim() || "";
        const title = statement.querySelector('[class$="_thmtitle"]')?.textContent.trim() || "";
        const item = document.createElement("li");
        const link = document.createElement("a");
        link.href = `#${statement.id}`;
        link.textContent = `${caption} ${number}${title ? ` · ${title}` : ""}`;
        item.append(link);
        list.append(item);
      }
      index.append(summary, list);
      const heading = main.querySelector(":scope > h1");
      if (heading) heading.after(index);
    }
  }

  document.querySelectorAll("nav.prev_up_next a[title]").forEach((link) => {
    link.setAttribute("aria-label", link.title);
    const label = document.createElement("span");
    label.className = "pager-label";
    label.textContent = link.querySelector(".icon-arrow-up") ? "Contents" : link.title;
    link.append(label);
  });

  document.querySelectorAll("nav.prev_up_next svg.showmore").forEach((icon) => {
    const label = icon.id === "showmore-plus" ? "Expand all proofs" : "Collapse all proofs";
    icon.setAttribute("role", "button");
    icon.setAttribute("tabindex", "0");
    icon.setAttribute("aria-label", label);
    icon.setAttribute("title", label);
    icon.addEventListener("keydown", (event) => {
      if (event.key === "Enter" || event.key === " ") {
        event.preventDefault();
        icon.dispatchEvent(new MouseEvent("click", { bubbles: true }));
      }
    });
  });

  document.querySelectorAll("div.proof_heading").forEach((heading) => {
    heading.setAttribute("role", "button");
    heading.setAttribute("tabindex", "0");
    heading.addEventListener("keydown", (event) => {
      if (event.key === "Enter" || event.key === " ") {
        event.preventDefault();
        heading.dispatchEvent(new MouseEvent("click", { bubbles: true }));
      }
    });
  });
});
