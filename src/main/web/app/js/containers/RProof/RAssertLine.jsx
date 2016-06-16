import { reduxForm } from 'redux-form'
import AssertLine from '../../components/Proof/AssertLine'
import { setProofStepType } from '../../actions'

const mapDispatchToProps = (dispatch) => (
  {
    onCloseClick: () => dispatch(setProofStepType(null))
  }
)

export default reduxForm({
  form: "addProofLine",
  fields: ["formula"],
  onSubmit: () => console.log('Making proof step!')
}, null, mapDispatchToProps)(AssertLine)

