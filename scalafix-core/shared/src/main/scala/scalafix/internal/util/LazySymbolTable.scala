package scalafix.internal.util

import scala.meta.internal.semanticdb3.Scala.Symbols
import java.io.InputStream
import java.net._
import java.nio.file._
import java.util.HashMap
import org.langmeta.internal.io.PathIO
import org.langmeta.io.AbsolutePath
import org.langmeta.io.Classpath
import scala.collection.concurrent.TrieMap
import scala.meta.internal.semanticdb3.Scala._
import scala.meta.internal.{semanticdb3 => s}

/**
  * Implementation of SymbolTable that lazily loads symbols on demand.
  *
  * @param mclasspath The classpath to load symbols from. Needs to be pre-processed by metacp,
  *                   see ClasspathOps.toMclasspath in scalafix-cli.
  */
class LazySymbolTable(mclasspath: Classpath) extends SymbolTable {

  // Map from symbols to the paths to their corresponding semanticdb file where they are stored.
  private val unloadedSymbols = TrieMap.empty[String, AbsolutePath]
  private val loadedSymbols = TrieMap.empty[String, s.SymbolInformation]
  private val semanticdb = "META-INF/semanticdb"
  private val semanticIdx = "META-INF/semanticdb.semanticidx"

  mclasspath.shallow.foreach(loadSemanticdbIndex)

  override def info(symbol: String): Option[s.SymbolInformation] = {
    var result = loadedSymbols.get(symbol)
    if (result.isEmpty) {
      loadSymbolFromClasspath(symbol)
      result = loadedSymbols.get(symbol)
      if (result.isEmpty && symbol.owner != Symbols.None) {
        info(symbol.owner)
        result = loadedSymbols.get(symbol)
      }
    }
    result
  }

  private def loadSymbolFromClasspath(symbol: String): Unit = {
    val toLoad = unloadedSymbols.get(symbol)
    if (toLoad.isDefined) {
      val in = toLoad.get.toNIO.toUri.toURL.openStream()
      val semanticdb =
        try s.TextDocuments.parseFrom(in)
        finally in.close()
      semanticdb.documents.foreach { document =>
        document.symbols.foreach { info =>
          loadedSymbols.put(info.symbol, info)
        }
      }
      unloadedSymbols.remove(symbol)
    }
  }

  private def loadIndex(root: AbsolutePath, in: InputStream): Unit = {
    val index =
      try s.Index.parseFrom(in)
      finally in.close()
    index.toplevels.foreach { toplevel =>
      unloadedSymbols.put(
        toplevel.symbol,
        root.resolve(semanticdb).resolve(toplevel.uri))
    }
  }

  private def loadSemanticdbIndex(root: AbsolutePath): Unit = {
    try {
      if (root.isDirectory) {
        loadIndex(root, Files.newInputStream(root.resolve(semanticIdx).toNIO))
      } else if (PathIO.extension(root.toNIO) == "jar") {
        val fs = {
          val map = new HashMap[String, String]()
          val uri = URI.create("jar:file:" + root.toNIO.toUri.getPath)
          try FileSystems.newFileSystem(uri, map)
          catch { case _: FileSystemAlreadyExistsException => FileSystems.getFileSystem(uri) }
        }
        try {
          val jarRoot = AbsolutePath(fs.getPath("/"))
          loadIndex(
            jarRoot,
            Files.newInputStream(jarRoot.resolve(semanticIdx).toNIO)
          )
        } finally {
          fs.close()
        }
      } else {
        throw new IllegalArgumentException(root.toString())
      }
    } catch {
      case _: NoSuchFileException =>
        ()
    }
  }

}
