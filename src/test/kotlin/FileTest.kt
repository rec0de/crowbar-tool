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
	"create"{
		val model = load(Paths.get("src/test/resources/create.abs"))
		val classDecl = extractClassDecl("Create","C", model)

		val sNode = extractMethodNode("success", classDecl)
		executeNode(sNode) shouldBe true

		val fNode = extractMethodNode("fail", classDecl)
		executeNode(fNode) shouldBe false
	}
})