import io.kotlintest.shouldBe
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.*
import java.nio.file.Paths

class FileTest : StringSpec ({
	"success"{
		val model = load(Paths.get("src/test/resources/success.abs"))
		val classDecl = extractClassDecl("Success","C", model)
		executeAll(classDecl) shouldBe true
	}
	"fails"{
		val model = load(Paths.get("src/test/resources/fail.abs"))
		val classDecl = extractClassDecl("Fail","C", model)

		val iNode = extractInitialNode(classDecl)
		executeNode(iNode) shouldBe false

		for(m in classDecl.methods){
			val node = extractMethodNode(m.methodSig.name, classDecl)
			executeNode(node) shouldBe false
		}
	}
})