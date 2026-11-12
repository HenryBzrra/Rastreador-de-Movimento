# Rastreador de Mouse

Registra o movimento e os cliques do mouse em segundo plano e mostra tudo em uma interface
escura e translúcida: **rastro**, **mapa de calor** e **timelapse** (GIF de até 1 minuto).

## Baixar e usar (sem instalar nada)

1. Abra a aba **Releases** deste repositório.
2. Baixe o arquivo do seu sistema:
   - Windows: `RastreadorMouse.exe`
   - macOS: `RastreadorMouse-macos.zip`
   - Linux: `RastreadorMouse-linux`
3. Dê dois cliques para abrir.

> **Windows:** como o programa não é assinado, o SmartScreen pode avisar. Clique em
> "Mais informações" → "Executar assim mesmo".
> **macOS:** clique com o botão direito no app → "Abrir" e libere o app em
> Ajustes → Privacidade e Segurança → Monitoramento de Entrada (e Acessibilidade).
> **Linux:** `chmod +x RastreadorMouse-linux` e execute. Funciona em X11.

## Como usar

| Ação | Atalho padrão (muda em **Ajustes**) |
|---|---|
| Iniciar / retomar | `F8` |
| Pausar | `F9` |
| Parar e salvar | `F10` |

Os atalhos funcionam com a janela minimizada. Ao parar, o rastro é salvo em **Cliques**
(imagem PNG + CSV com todos os eventos).

- **Rastreio**: o risco do movimento e um ponto por clique. Cliques múltiplos viram anéis com o número (×2, ×3…).
- **Calor**: mapa de calor contínuo. A suavização se ajusta em Ajustes.
- **Timelapse**: reproduz a sessão acelerada em no máximo 60 s e exporta como GIF.
- **Cliques**: galeria das sessões salvas (renomear, exportar, excluir, abrir o timelapse).
- **Perfil**: nome e foto.

Os dados ficam na sua máquina, em `~/.rastreador_mouse`.

## Rodar pelo código

```bash
pip install -r requirements.txt
python rastreador_mouse.py
```

## Gerar o executável você mesmo

```bash
pip install -r requirements.txt pyinstaller
pyinstaller --noconfirm --onefile --windowed --name RastreadorMouse --collect-submodules pynput rastreador_mouse.py
```

O resultado fica em `dist/`. No macOS, remova `--onefile` (gera um `.app`).

## Releases automáticos

Ao enviar uma tag `v*` (por exemplo `git tag v1.0.0 && git push origin v1.0.0`), o GitHub Actions
compila para Windows, macOS e Linux e publica os arquivos na aba Releases
(`.github/workflows/build.yml`).

## Privacidade

O programa grava a posição e os cliques do mouse **em todo o sistema**, mas não grava teclas
digitadas nem envia nada pela rede. Use apenas no seu computador ou com o consentimento de quem o usa.

## Licença

MIT
