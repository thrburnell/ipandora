import { reduxForm } from 'redux-form'
import AssumeLine from '../../components/InductiveCase/AssumeLine'
import { closeInductiveCaseProofStep, makeAssumption } from '../../actions'

const mapDispatchToProps = (dispatch) => (
  {
    onCloseClick: () => dispatch(closeInductiveCaseProofStep())
  }
)

const submit = (values, dispatch) => {
  return new Promise((resolve, reject) => {
    console.log("Not yet implemented")
    reject()

    // if (!values.formula) {
    //   reject({ formula: "Undefined" })
    // } else {
    //   dispatch(makeAssumption(values.formula, "INDUCTIVE_CASE"))
    //     .then(() => resolve())
    //     .catch(() => reject({ formula: "Invalid" }))
    // }
  })
}

export default reduxForm({
  form: "addInductiveCaseAssumeLine",
  fields: ["formula"],
  onSubmit: submit
}, null, mapDispatchToProps)(AssumeLine)

