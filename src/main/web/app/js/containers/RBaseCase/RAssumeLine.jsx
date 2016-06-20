import { reduxForm } from 'redux-form'
import AssumeLine from '../../components/BaseCase/AssumeLine'
import { closeBaseCaseProofStep, makeAssumption } from '../../actions'

const mapDispatchToProps = (dispatch) => (
  {
    onCloseClick: () => dispatch(closeBaseCaseProofStep())
  }
)

const submit = (values, dispatch) => {
  return new Promise((resolve, reject) => {
    console.log("Not yet implemented")
    reject()

    // if (!values.formula) {
    //   reject({ formula: "Undefined" })
    // } else {
    //   dispatch(makeAssumption(values.formula, "BASE_CASE"))
    //     .then(() => resolve())
    //     .catch(() => reject({ formula: "Invalid" }))
    // }
  })
}

export default reduxForm({
  form: "addBaseCaseAssumeLine",
  fields: ["formula"],
  onSubmit: submit
}, null, mapDispatchToProps)(AssumeLine)

