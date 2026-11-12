//! `bibliography <references.yml> <output.json>` writes every entry of the Hayagriva bibliography
//! `references.yml` to `output.json`, as an object from citation keys to the entry formatted in
//! the APA style as HTML. The list of open problems (`../index.html`) shows it next to every
//! citation `- [KEY, locator]` of a docstring.

use std::{env, fs, process::ExitCode};

use hayagriva::archive::{ArchivedStyle, locales};
use hayagriva::citationberg::Style;
use hayagriva::{
    BibliographyDriver, BibliographyRequest, BufWriteFormat, CitationItem, CitationRequest,
};

fn run(input: &str, output: &str) -> Result<usize, String> {
    let yaml = fs::read_to_string(input).map_err(|e| format!("cannot read {input}: {e}"))?;
    let library = hayagriva::io::from_yaml_str(&yaml).map_err(|e| format!("{input}: {e}"))?;
    let Style::Independent(style) = ArchivedStyle::AmericanPsychologicalAssociation.get() else {
        return Err("the APA style is not an independent CSL style".into());
    };
    let locales = locales();
    // An entry is rendered in the bibliography only once it is cited.
    let mut driver = BibliographyDriver::new();
    for entry in library.iter() {
        driver.citation(CitationRequest::from_items(
            vec![CitationItem::with_entry(entry)],
            &style,
            &locales,
        ));
    }
    let rendered = driver.finish(BibliographyRequest {
        style: &style,
        locale: None,
        locale_files: &locales,
    });
    let items = rendered.bibliography.map(|b| b.items).unwrap_or_default();
    let mut out = serde_json::Map::new();
    for item in items {
        let mut html = String::new();
        item.content
            .write_buf(&mut html, BufWriteFormat::Html)
            .map_err(|e| format!("cannot format {}: {e}", item.key))?;
        out.insert(item.key, html.into());
    }
    let count = out.len();
    let json = serde_json::to_string_pretty(&out).map_err(|e| e.to_string())?;
    fs::write(output, json + "\n").map_err(|e| format!("cannot write {output}: {e}"))?;
    Ok(count)
}

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();
    let [_, input, output] = args.as_slice() else {
        eprintln!("usage: bibliography <references.yml> <output.json>");
        return ExitCode::FAILURE;
    };
    match run(input, output) {
        Ok(count) => {
            println!("bibliography: wrote {count} entries to {output}");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("bibliography: {e}");
            ExitCode::FAILURE
        }
    }
}
